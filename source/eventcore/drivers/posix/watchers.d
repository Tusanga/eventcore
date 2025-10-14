module eventcore.drivers.posix.watchers;
@safe:

import eventcore.driver;
import eventcore.drivers.posix.driver;
import eventcore.internal.ioworker;
import eventcore.internal.utils : mallocT, freeT, nogc_assert, mallocNT;
import eventcore.internal.dlist : StackDList;


final class InotifyEventDriverWatchers(Events : EventDriverEvents) : EventDriverWatchers
{
	import core.stdc.errno : errno, EAGAIN, EINPROGRESS;
	import core.sys.posix.fcntl, core.sys.posix.unistd, core.sys.linux.sys.inotify;
	import core.sync.mutex : Mutex;
	import std.algorithm.comparison : among;
	import std.file;

	private {
		alias Loop = typeof(Events.init.loop);

		enum EVENTS = IN_CREATE | IN_DELETE | IN_DELETE_SELF | IN_MODIFY |
			IN_MOVE_SELF | IN_MOVED_FROM | IN_MOVED_TO;

		struct Watch {
			Watch* parent, prev, next;
			StackDList!Watch children;
			string name;
			int id;

			@property string path()
			const @safe nothrow {
				// TODO: use just one allocation
				return parent && parent.name.length ? parent.path() ~ "/" ~ name : name;
			}
		}

		struct WatcherState {
			Watch* watch;
			Watch*[int] watches; // TODO: use a @nogc (allocator based) map
			string basePath;
			bool recursive;

			@disable this(this);
		}

		Loop m_loop;
		Mutex m_mutex;
		WatcherState[WatcherID] m_watchers; // TODO: use a @nogc (allocator based) map
		IOWorkerPool m_workerPool;
		StackDList!Watch m_freeList;
	}

	this(Events events)
	nothrow @nogc {
		m_loop = events.loop;
		m_mutex = mallocT!Mutex();
	}

	void dispose()
	@trusted {
		m_workerPool = IOWorkerPool.init;
		destroy(m_mutex);
	}

	final override WatcherID watchDirectory(string path, bool recursive, FileChangesCallback callback)
	{
		import std.path : buildPath, pathSplitter;
		import std.range : drop;
		import std.range.primitives : walkLength;

		enum IN_NONBLOCK = 0x800; // value in core.sys.linux.sys.inotify is incorrect
		auto handle = () @trusted { return inotify_init1(IN_NONBLOCK | IN_CLOEXEC); } ();
		if (handle == -1) return WatcherID.invalid;

		auto ret = m_loop.initFD!WatcherID(handle, FDFlags.none, WatcherSlot(callback));
		m_loop.registerFD(cast(FD)ret, EventMask.read);
		m_loop.setNotifyCallback!(EventType.read)(cast(FD)ret, &onChanges);

		m_mutex.lock_nothrow();
		m_watchers[ret] = WatcherState(basePath: path, recursive: recursive);
		m_mutex.unlock_nothrow();
		addWatchRecursively(ret, -1, null);

		processEvents(ret);

		return ret;
	}

	final override bool isValid(WatcherID handle)
	const {
		if (handle.value >= m_loop.m_fds.length) return false;
		return m_loop.m_fds[handle.value].common.validationCounter == handle.validationCounter;
	}

	final override void addRef(WatcherID descriptor)
	{
		if (!isValid(descriptor)) return;
		assert(m_loop.m_fds[descriptor].common.refCount > 0, "Adding reference to unreferenced event FD.");
		m_loop.m_fds[descriptor].common.refCount++;
	}

	final override bool releaseRef(WatcherID descriptor)
	{
		if (!isValid(descriptor)) return true;

		FD fd = cast(FD)descriptor;
		auto slot = () @trusted { return &m_loop.m_fds[fd]; } ();
		nogc_assert(slot.common.refCount > 0, "Releasing reference to unreferenced event FD.");
		if (--slot.common.refCount == 1) { // NOTE: 1 because setNotifyCallback increments the reference count
			m_loop.setNotifyCallback!(EventType.read)(fd, null);
			m_loop.unregisterFD(fd, EventMask.read);
			m_loop.clearFD!WatcherSlot(fd);
			m_mutex.lock_nothrow();
			m_watchers.remove(descriptor);
			m_mutex.unlock_nothrow();
			/*errnoEnforce(*/close(cast(int)fd)/* == 0)*/;
			return false;
		}

		return true;
	}

	final protected override void* rawUserData(WatcherID descriptor, size_t size, DataInitializer initialize, DataInitializer destroy)
	@system {
		if (!isValid(descriptor)) return null;
		return m_loop.rawUserDataImpl(descriptor, size, initialize, destroy);
	}

	private void onChanges(FD fd)
	{
		processEvents(cast(WatcherID)fd);
	}

	private void processEvents(WatcherID id)
	{
		import core.stdc.stdio : FILENAME_MAX;
		import core.stdc.string : strlen;

		ubyte[inotify_event.sizeof + FILENAME_MAX + 1] buf = void;
		while (true) {
			auto ret = () @trusted { return read(cast(int)id, &buf[0], buf.length); } ();

			if (ret == -1 && errno.among!(EAGAIN, EINPROGRESS))
				break;
			assert(ret <= buf.length);

			auto rem = buf[0 .. ret];
			while (rem.length > 0) {
				auto ev = () @trusted { return cast(inotify_event*)rem.ptr; } ();
				rem = rem[inotify_event.sizeof + ev.len .. $];

				// is the watch already deleted?
				if (ev.mask & IN_IGNORED) continue;

				// if the directory for the watch gets deleted or moved, clean
				// up all watches
				if (ev.mask & (IN_DELETE_SELF|IN_MOVE_SELF)) {
					removeWatchRecursively(id, ev.wd);
					continue;
				}

				auto name = () @trusted { return ev.name.ptr[0 .. strlen(ev.name.ptr)]; } ();

				FileChange ch;
				if (ev.mask & (IN_CREATE|IN_MOVED_TO)) {
					ch.kind = FileChangeKind.added;
				} else if (ev.mask & (IN_DELETE|IN_MOVED_FROM)) {
					ch.kind = FileChangeKind.removed;
				} else if (ev.mask & IN_MODIFY) {
					ch.kind = FileChangeKind.modified;
				}

				string base_path, sub_path;
				bool add_watch;

				{
					m_mutex.lock_nothrow();
					scope (exit) m_mutex.unlock_nothrow();
					auto watcher = &m_watchers[id];
					if (!watcher) return;
					auto pwatch = ev.wd in watcher.watches;
					if (!pwatch) continue;
					base_path = watcher.basePath;
					sub_path = (*pwatch).path;
					add_watch = ch.kind == FileChangeKind.added && watcher.recursive && (ev.mask & IN_ISDIR);
				}

				if (add_watch)
					addWatchRecursively(id, ev.wd, name.idup);

				ch.baseDirectory = base_path;
				ch.directory = sub_path;
				ch.name = name;
				addRef(id); // assure that the id doesn't get invalidated until after the callback
				auto cb = m_loop.m_fds[id].watcher.callback;
				cb(id, ch);
				if (!releaseRef(id)) return;
			}
		}
	}

	private void removeWatchRecursively(WatcherID id, int watch)
	{
		m_mutex.lock_nothrow();
		scope (exit) m_mutex.unlock_nothrow();

		auto watcher = &m_watchers[id];

		void remove(Watch* watch)
		@safe nothrow {
			foreach (subwatch; watch.children)
				remove(subwatch);

			() @trusted { inotify_rm_watch(cast(int)id, watch.id); } ();

			if (watch.parent) watch.parent.children.remove(watch);
			else watcher.watch = null;

			freeWatch(watch);
		}

		if (auto pw = watch in watcher.watches)
			remove(*pw);
	}

	private void addWatchRecursively(WatcherID id, int watch, string name)
	@trusted {
		static void wrapper(InotifyEventDriverWatchers driver, WatcherID id, int watch, string name) {
			driver.addWatchRecursivelySync(id, watch, name);
		}

		// add the base watch immediately to guarantee detecting changes
		// directly within the folder
		bool is_recursive;
		string path;
		auto wd = addWatch(id, watch, name, is_recursive, path);

		if (is_recursive) {
			setupThreadPool();
			m_workerPool.run!wrapper(this, id, watch, name);
		}
	}

	private void addWatchRecursivelySync(WatcherID id, int watch, string name)
	@safe {
		import std.path : baseName;

		bool is_recursive;
		string path;
		auto wd = addWatch(id, watch, name, is_recursive, path);
		if (wd < 0) return;

		if (is_recursive) {
			try () @trusted {
				foreach (de; path.dirEntries(SpanMode.shallow))
					if (de.isDir)
						addWatchRecursivelySync(id, wd, baseName(de.name));
			} ();
			catch (Exception e) {}
		}
	}

	private int addWatch(WatcherID id, int watch, string name, out bool is_recursive, out string path)
	{
		import std.path : buildPath;
		import std.string : toStringz;

		{ // determine full path for watch
			m_mutex.lock_nothrow();
			scope (exit) m_mutex.unlock_nothrow();
			auto watcher = id in m_watchers;
			if (!watcher) return -1;

			is_recursive = watcher.recursive;
			if (watch >= 0) {
				auto pw = watch in watcher.watches;
				if (!pw) return -1;
				path = buildPath(watcher.basePath, (*pw).path, name);
			} else {
				assert(name.length == 0);
				path = watcher.basePath;
			}
		}

		// create the new watch
		immutable wd = () @trusted { return inotify_add_watch(cast(int)id, path.toStringz, EVENTS); } ();
		if (wd == -1) return -1;


		{ // register watch in watcher slot
			m_mutex.lock_nothrow();
			scope (exit) m_mutex.unlock_nothrow();

			auto watcher = id in m_watchers;
			if (!watcher) return -1;

			// already registered?
			if (wd in watcher.watches)
				return wd;

			auto wst = allocWatch();
			wst.id = wd;
			wst.name = name;
			if (watch >= 0)  {
				auto pw = watch in watcher.watches;
				if (!pw) {
					freeWatch(wst);
					return -1;
				}

				wst.parent = *pw;
				(*pw).children.insertBack(wst);
			} else {
				watcher.watch = wst;
			}
			watcher.watches[wd] = wst;
		}

		return wd;
	}

	Watch* allocWatch()
	{
		if (m_freeList.empty) {
			auto reserve = mallocNT!Watch(2048);
			foreach (i; 0 .. reserve.length)
				m_freeList.insertBack(&reserve[i]);
		}

		auto ret = m_freeList.back;
		m_freeList.removeBack();
		return ret;
	}
	void freeWatch(Watch* ws)
	{
		*ws = Watch.init;
		m_freeList.insertBack(ws);
	}

	private void setupThreadPool()
	{
		if (!m_workerPool)
			m_workerPool = acquireIOWorkerPool();
	}
}

version (OSX) // NOTE: Although this works on iOS, too, this is a private API there
final class FSEventsEventDriverWatchers(Events : EventDriverEvents) : EventDriverWatchers {
@safe: /*@nogc:*/ nothrow:
	import eventcore.internal.corefoundation;
	import eventcore.internal.coreservices;
	import std.string : toStringz;

	private {
		static struct WatcherSlot {
			FSEventStreamRef stream;
			string path;
			string fullPath;
			FileChangesCallback callback;
			WatcherID id;
			int refCount = 1;
			bool recursive;
			FSEventStreamEventId lastEvent;
			ubyte[16 * size_t.sizeof] userData;
			DataInitializer userDataDestructor;
		}
		//HashMap!(void*, WatcherSlot) m_watches;
		WatcherSlot[WatcherID] m_watches;
		WatcherID[void*] m_streamMap;
		Events m_events;
		size_t m_handleCounter = 1;
		uint m_validationCounter;
	}

	this(Events events) { m_events = events; }

	void dispose()
	{
	}

	final override WatcherID watchDirectory(string path, bool recursive, FileChangesCallback on_change)
	@trusted {
		import std.file : isSymlink, readLink;
		import std.path : absolutePath, buildPath, buildNormalizedPath, dirName, pathSplitter;

		FSEventStreamContext ctx;
		ctx.info = () @trusted { return cast(void*)this; } ();

		static string resolveSymlinks(string path)
		{
			string res;
			foreach (ps; path.pathSplitter) {
				if (!res.length) res = ps;
				else res = buildPath(res, ps);
				if (isSymlink(res)) {
					res = readLink(res).absolutePath(dirName(res));
				}
			}
			return res.buildNormalizedPath;
		}

		string abspath;
		try abspath = resolveSymlinks(absolutePath(path));
		catch (Exception e) {
			return WatcherID.invalid;
		}

		if (m_handleCounter == 0) {
			m_handleCounter++;
			m_validationCounter++;
		}
		auto id = WatcherID(cast(size_t)m_handleCounter++, m_validationCounter);

		WatcherSlot slot = {
			path: path,
			fullPath: abspath,
			callback: on_change,
			id: id,
			recursive: recursive,
			lastEvent: kFSEventStreamEventIdSinceNow
		};

		startStream(slot, kFSEventStreamEventIdSinceNow);

		m_events.loop.m_waiterCount++;
		m_watches[id] = slot;
		return id;
	}

	final override bool isValid(WatcherID handle)
	const {
		return !!(handle in m_watches);
	}

	final override void addRef(WatcherID descriptor)
	{
		if (!isValid(descriptor)) return;

		auto slot = descriptor in m_watches;
		slot.refCount++;
	}

	final override bool releaseRef(WatcherID descriptor)
	{
		if (!isValid(descriptor)) return true;

		auto slot = descriptor in m_watches;
		if (!--slot.refCount) {
			destroyStream(slot.stream);
			m_watches.remove(descriptor);
			m_events.loop.m_waiterCount--;
			return false;
		}

		return true;
	}

	final protected override void* rawUserData(WatcherID descriptor, size_t size, DataInitializer initialize, DataInitializer destroy)
	@system {
		if (!isValid(descriptor)) return null;

		auto slot = descriptor in m_watches;

		if (size > WatcherSlot.userData.length) assert(false);
		if (!slot.userDataDestructor) {
			initialize(slot.userData.ptr);
			slot.userDataDestructor = destroy;
		}
		return slot.userData.ptr;
	}

	private static extern(C) void onFSEvent(ConstFSEventStreamRef streamRef,
		void* clientCallBackInfo, size_t numEvents, void* eventPaths,
		const(FSEventStreamEventFlags)* eventFlags,
		const(FSEventStreamEventId)* eventIds)
	{
		import std.conv : to;
		import std.path : asRelativePath, baseName, dirName;

		if (!numEvents) return;

		auto this_ = () @trusted { return cast(FSEventsEventDriverWatchers)clientCallBackInfo; } ();
		auto h = () @trusted { return cast(void*)streamRef; } ();
		auto ps = h in this_.m_streamMap;
		if (!ps) return;
		auto id = *ps;
		auto slot = id in this_.m_watches;

		auto patharr = () @trusted { return (cast(const(char)**)eventPaths)[0 .. numEvents]; } ();
		auto flagsarr = () @trusted { return eventFlags[0 .. numEvents]; } ();
		auto idarr = () @trusted { return eventIds[0 .. numEvents]; } ();

		if (flagsarr[0] & kFSEventStreamEventFlagHistoryDone) {
			if (!--numEvents) return;
			patharr = patharr[1 .. $];
			flagsarr = flagsarr[1 .. $];
			idarr = idarr[1 .. $];
		}

		// A new stream needs to be created after every change, because events
		// get coalesced per file (event flags get or'ed together) and it becomes
		// impossible to determine the actual event
		this_.startStream(*slot, idarr[$-1]);

		foreach (i; 0 .. numEvents) {
			auto pathstr = () @trusted { return to!string(patharr[i]); } ();
			auto f = flagsarr[i];

			string rp;
			try rp = pathstr.asRelativePath(slot.fullPath).to!string;
			catch (Exception e) assert(false, e.msg);

			if (rp == "." || rp == "") continue;

			FileChange ch;
			ch.baseDirectory = slot.path;
			ch.directory = dirName(rp);
			ch.name = baseName(rp);

			if (ch.directory == ".") ch.directory = "";

			if (!slot.recursive && ch.directory != "") continue;

			void emit(FileChangeKind k)
			{
				ch.kind = k;
				slot.callback(id, ch);
			}

			import std.file : exists;
			bool does_exist = exists(pathstr);

			// The order of tests is important to properly lower the more
			// complex flags system to the three event types provided by
			// eventcore
			if (f & kFSEventStreamEventFlagItemRenamed) {
				if (!does_exist) emit(FileChangeKind.removed);
				else emit(FileChangeKind.added);
			} else if (f & kFSEventStreamEventFlagItemRemoved && !does_exist) {
				emit(FileChangeKind.removed);
			} else if (f & kFSEventStreamEventFlagItemModified && does_exist) {
				emit(FileChangeKind.modified);
			} else if (f & kFSEventStreamEventFlagItemCreated && does_exist) {
				emit(FileChangeKind.added);
			}
		}
	}

	private void startStream(ref WatcherSlot slot, FSEventStreamEventId since_when)
	@trusted {
		if (slot.stream) {
			destroyStream(slot.stream);
			slot.stream = null;
		}

		FSEventStreamContext ctx;
		ctx.info = () @trusted { return cast(void*)this; } ();

		auto pstr = CFStringCreateWithBytes(null,
			cast(const(ubyte)*)slot.path.ptr, slot.path.length,
			kCFStringEncodingUTF8, false);
		scope (exit) CFRelease(pstr);
		auto paths = CFArrayCreate(null, cast(const(void)**)&pstr, 1, null);
		scope (exit) CFRelease(paths);

		slot.stream = FSEventStreamCreate(null, &onFSEvent, () @trusted { return &ctx; } (),
			paths, since_when, 0.1, kFSEventStreamCreateFlagFileEvents|kFSEventStreamCreateFlagNoDefer);
		FSEventStreamScheduleWithRunLoop(slot.stream, CFRunLoopGetCurrent(), kCFRunLoopDefaultMode);
		FSEventStreamStart(slot.stream);

		m_streamMap[cast(void*)slot.stream] = slot.id;
	}

	private void destroyStream(FSEventStreamRef stream)
	@trusted {
		FSEventStreamStop(stream);
		FSEventStreamInvalidate(stream);
		FSEventStreamRelease(stream);
		m_streamMap.remove(cast(void*)stream);
	}
}


/** Generic directory watcher implementation based on periodic directory
	scanning.

	Note that this implementation, although it works on all operating systems,
	is not efficient for directories with many files, since it has to keep a
	representation of the whole directory in memory and needs to list all files
	for each polling period, which can result in excessive hard disk activity.
*/
final class PollEventDriverWatchers(Events : EventDriverEvents) : EventDriverWatchers {
@safe: /*@nogc:*/ nothrow:
	import core.thread : Thread;
	import core.sync.mutex : Mutex;

	private {
		Events m_events;
		PollingThread[EventID] m_pollers;
	}

	this(Events events)
	@nogc {
		m_events = events;
	}

	void dispose()
	@trusted {
		foreach (pt; m_pollers.byValue) {
			pt.dispose();
			try pt.join();
			catch (Exception e) {
				// not bringing down the application here, because not being
				// able to join the thread here likely isn't a problem
			}
		}
	}

	final override WatcherID watchDirectory(string path, bool recursive, FileChangesCallback on_change)
	{
		import std.file : exists, isDir;

		// validate base directory
		try if (!isDir(path)) return WatcherID.invalid;
		catch (Exception e) return WatcherID.invalid;

		// create event to wait on for new changes
		auto evt = m_events.create();
		assert(evt !is EventID.invalid, "Failed to create event.");
		auto pt = new PollingThread(() @trusted { return cast(shared)m_events; } (), evt, path, recursive, on_change);
		m_pollers[evt] = pt;
		try () @trusted { pt.isDaemon = true; } ();
		catch (Exception e) assert(false, e.msg);
		() @trusted { pt.start(); } ();

		m_events.wait(evt, &onEvent);

		return cast(WatcherID)evt;
	}

	final override bool isValid(WatcherID handle)
	const {
		return m_events.isValid(cast(EventID)handle);
	}

	final override void addRef(WatcherID descriptor)
	{
		if (!isValid(descriptor)) return;

		auto evt = cast(EventID)descriptor;
		auto pt = evt in m_pollers;
		assert(pt !is null);
		m_events.addRef(evt);
	}

	final override bool releaseRef(WatcherID descriptor)
	{
		if (!isValid(descriptor)) return true;

		auto evt = cast(EventID)descriptor;
		auto pt = evt in m_pollers;
		nogc_assert(pt !is null, "Directory watcher polling thread does not exist");
		if (!m_events.releaseRef(evt)) {
			pt.dispose();
			m_pollers.remove(evt);
			return false;
		}
		return true;
	}

	final protected override void* rawUserData(WatcherID descriptor, size_t size, DataInitializer initialize, DataInitializer destroy)
	@system {
		return m_events.loop.rawUserDataImpl(cast(EventID)descriptor, size, initialize, destroy);
	}

	private void onEvent(EventID evt)
	{
		auto pt = evt in m_pollers;
		if (!pt) return;

		m_events.wait(evt, &onEvent);

		foreach (ref ch; pt.readChanges())
			pt.m_callback(cast(WatcherID)evt, ch);
	}


	private final class PollingThread : Thread {
		private {
			shared(Events) m_eventsDriver;
			Mutex m_changesMutex;
			/*shared*/ FileChange[] m_changes; // protected by m_changesMutex
			EventID m_changesEvent; // protected by m_changesMutex
			immutable string m_basePath;
			immutable bool m_recursive;
			immutable FileChangesCallback m_callback;
		}

		this(shared(Events) event_driver, EventID event, string path, bool recursive, FileChangesCallback callback)
		@trusted nothrow {
			import core.time : seconds;

			m_changesMutex = new Mutex;
			m_eventsDriver = event_driver;
			m_changesEvent = event;
			m_basePath = path;
			m_recursive = recursive;
			m_callback = callback;

			try super(&run);
			catch (Exception e) assert(false, e.msg);
		}

		void dispose()
		nothrow {
			try synchronized (m_changesMutex) {
				m_changesEvent = EventID.invalid;
			} catch (Exception e) assert(false, e.msg);
		}

		FileChange[] readChanges()
		nothrow {
			import std.algorithm.mutation : swap;

			FileChange[] changes;
			try synchronized (m_changesMutex)
				swap(changes, m_changes);
			catch (Exception e) assert(false, "Failed to acquire mutex: "~e.msg);
			return changes;
		}

		private void run()
		nothrow @trusted {
			import core.time : MonoTime, msecs;
			import std.algorithm.comparison : min;

			auto poller = new DirectoryPoller(m_basePath, m_recursive, (ch) {
				try synchronized (m_changesMutex) {
					m_changes ~= ch;
				} catch (Exception e) assert(false, "Mutex lock failed: "~e.msg);
			});

			poller.scan(false);

			try while (true) {
				auto timeout = MonoTime.currTime() + min(poller.entryCount, 60000).msecs + 1000.msecs;
				while (true) {
					try synchronized (m_changesMutex) {
						if (m_changesEvent == EventID.invalid) return;
					} catch (Exception e) assert(false, "Mutex lock failed: "~e.msg);
					auto remaining = timeout - MonoTime.currTime();
					if (remaining <= 0.msecs) break;
					sleep(min(1000.msecs, remaining));
				}

				poller.scan(true);

				try synchronized (m_changesMutex) {
					if (m_changesEvent == EventID.invalid) return;
					if (m_changes.length)
						m_eventsDriver.trigger(m_changesEvent, false);
				} catch (Exception e) assert(false, "Mutex lock failed: "~e.msg);
			} catch (Throwable th) {
				import core.stdc.stdio : fprintf, stderr;
				import core.stdc.stdlib : abort;

				fprintf(stderr, "Fatal error: %.*s\n",
						cast(int) th.msg.length, th.msg.ptr);
				abort();
			}
		}

	}

	private final class DirectoryPoller {
		private final static class Entry {
			Entry parent;
			string name;
			ulong size;
			long lastChange;

			this(Entry parent, string name, ulong size, long lastChange)
			{
				this.parent = parent;
				this.name = name;
				this.size = size;
				this.lastChange = lastChange;
			}

			string path()
			{
				import std.path : buildPath;
				if (parent)
					return buildPath(parent.path, name);
				else return name;
			}

			bool isDir() const { return size == ulong.max; }
		}

		private struct Key {
			Entry parent;
			string name;
		}

		alias ChangeCallback = void delegate(FileChange) @safe nothrow;

		private {
			immutable string m_basePath;
			immutable bool m_recursive;

			Entry[Key] m_entries;
			size_t m_entryCount;
			ChangeCallback m_onChange;
		}

		this(string path, bool recursive, ChangeCallback on_change)
		{
			m_basePath = path;
			m_recursive = recursive;
			m_onChange = on_change;
		}

		@property size_t entryCount() const { return m_entryCount; }

		private void addChange(FileChangeKind kind, Key key)
		{
			m_onChange(FileChange(kind, m_basePath, key.parent ? key.parent.path : "", key.name));
		}

		private void scan(bool generate_changes)
		@trusted nothrow {
			import std.algorithm.mutation : swap;

			Entry[Key] new_entries;
			Entry[] added;
			size_t ec = 0;

			scan(null, generate_changes, new_entries, added, ec);

			// detect all roots of removed sub trees
			foreach (e; m_entries.byKeyValue) {
				if (!e.key.parent || Key(e.key.parent.parent, e.key.parent.name) !in m_entries) {
					if (generate_changes)
						addChange(FileChangeKind.removed, e.key);
				}
			}

			foreach (e; added)
				addChange(FileChangeKind.added, Key(e.parent, e.name));

			swap(m_entries, new_entries);
			m_entryCount = ec;

			// clear all left-over entries (delted directly or indirectly)
			foreach (e; new_entries.byValue) {
				try freeT(e);
				catch (Exception e) assert(false, e.msg);
			}
		}

		private void scan(Entry parent, bool generate_changes, ref Entry[Key] new_entries, ref Entry[] added, ref size_t ec)
		@trusted nothrow {
			import std.file : SpanMode, dirEntries;
			import std.path : buildPath, baseName;

			auto ppath = parent ? buildPath(m_basePath, parent.path) : m_basePath;
			try foreach (de; dirEntries(ppath, SpanMode.shallow)) {
				auto key = Key(parent, de.name.baseName);
				auto modified_time = de.timeLastModified.stdTime;
				if (auto pe = key in m_entries) {
					if ((*pe).isDir) {
						if (m_recursive)
							scan(*pe, generate_changes, new_entries, added, ec);
					} else {
						if ((*pe).size != de.size || (*pe).lastChange != modified_time) {
							if (generate_changes)
								addChange(FileChangeKind.modified, key);
							(*pe).size = de.size;
							(*pe).lastChange = modified_time;
						}
					}

					new_entries[key] = *pe;
					ec++;
					m_entries.remove(key);
				} else {
					auto e = mallocT!Entry(parent, key.name, de.isDir ? ulong.max : de.size, modified_time);
					new_entries[key] = e;
					ec++;
					if (generate_changes) added ~= e;

					if (de.isDir && m_recursive) scan(e, false, new_entries, added, ec);
				}
			} catch (Exception e) {} // will result in all children being flagged as removed
		}
	}
}

package struct WatcherSlot {
	alias Handle = WatcherID;
	FileChangesCallback callback;
}

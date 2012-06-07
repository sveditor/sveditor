/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.io.RandomAccessFile;
import java.lang.ref.Reference;
import java.lang.ref.SoftReference;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;
import net.sf.sveditor.core.job_mgr.IJob;
import net.sf.sveditor.core.job_mgr.IJobMgr;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;

@SuppressWarnings({"rawtypes","unchecked"})
public class SVDBThreadedFileIndexCache implements ISVDBIndexCache, ILogLevelListener {
	private String							fBaseLocation;
	private Map<String, CacheFileInfo>		fFileCache;
	private ISVDBFS							fSVDBFS;
	private Object							fIndexData;
	private LogHandle						fLog;
	private List<IDBReader>					fPersistenceRdrSet;
	private List<IDBWriter>					fPersistenceWriterSet;
	private long							fNumFilesRead = 0;
	private boolean						fDebugEn = false;
	private List<IJob>						fWritebackJobs;

	private int							fMaxCacheSize = 50;
	
	private static CacheFileInfo			fCacheHead;
	private static CacheFileInfo			fCacheTail;
	private static int					fCacheSize;
	
	private boolean						fUseSoftRef = true;

	final class CacheFileInfo {
		public boolean						fCached;
		public String						fPath;
		public CacheFileInfo				fPrev;
		public CacheFileInfo				fNext;
		public Reference<SVDBFile>			fSVDBPreProcFile;
		public SVDBFile						fSVDBPreProcFileRef;
		public Reference<SVDBFileTree>		fSVDBFileTree;
		public SVDBFileTree					fSVDBFileTreeRef;
		public Reference<SVDBFile>			fSVDBFile;
		public SVDBFile						fSVDBFileRef;
		public Reference<List<SVDBMarker>>	fMarkers;
		public List<SVDBMarker>				fMarkersRef;
		public long						fLastModified;
		
		public CacheFileInfo(String path) {
			fPath = path;
			fSVDBPreProcFile = (Reference<SVDBFile>)createRef(null);
			fSVDBFileTree = (Reference<SVDBFileTree>)createRef(null);
			fSVDBFile = (Reference<SVDBFile>)createRef(null);
			fMarkers = (Reference<List<SVDBMarker>>)createRef(null);
			fLastModified = -1;
		}
	}
	
	public SVDBThreadedFileIndexCache(ISVDBFS fs) {
		fSVDBFS = fs;
		fFileCache = new HashMap<String, SVDBThreadedFileIndexCache.CacheFileInfo>();
		fLog = LogFactory.getLogHandle("SVDBFileIndexCache");
		fDebugEn = fLog.isEnabled();
		fLog.addLogLevelListener(this);
		fPersistenceRdrSet = new ArrayList<IDBReader>(); 
		fPersistenceWriterSet = new ArrayList<IDBWriter>();
		fWritebackJobs = new ArrayList<IJob>();
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	public long numFilesRead() {
		return fNumFilesRead;
	}

	public void removeStoragePath(List<File> db_path_list) {
		fSVDBFS.removeStoragePath(db_path_list);
	}

	public void setIndexData(Object data) {
		fIndexData = data;
	}

	public Object getIndexData() {
		return fIndexData;
	}

	public boolean isValid() {
		// TODO Auto-generated method stub
		return true;
	}
	
	public void clear() {
		// Delete entire index
		if (fDebugEn) {
			fLog.debug("clear");
		}
		fFileCache.clear();
		fSVDBFS.delete("");
	}

	public void addFile(String path) {
		getCacheFileInfo(path, true);
	}
	
	private CacheFileInfo getCacheFileInfo(String path, boolean create) {
		synchronized (fFileCache) {
			CacheFileInfo file = null;
			if (!fFileCache.containsKey(path)) {
				if (create) {
					file = new CacheFileInfo(path);
					fFileCache.put(path, file);
				}
			} else {
				file = fFileCache.get(path);
				
			}
			if (file != null) {
				if (file.fCached) {
					moveElementToTail(file);
				} else {
					addElementToTail(file);
				}
			}
			return file;
		}
	}
	
	public void setMarkers(String path, List<SVDBMarker> markers) {
		CacheFileInfo cfi = getCacheFileInfo(path, true);

		cfi.fMarkers = (Reference<List<SVDBMarker>>)createRef(markers);
		
		// We know we're referenced, so update the links
		cfi.fMarkersRef = markers;
	}
	
	public List<SVDBMarker> getMarkers(String path) {
		CacheFileInfo cfi = getCacheFileInfo(path, false);
		
		List<SVDBMarker> m = (cfi != null)?cfi.fMarkers.get():null;
		if (m == null) {
			String parent_dir = computePathDir(path);
			String target_file = parent_dir + "/markers";
			if (fSVDBFS.fileExists(target_file)){
				cfi = getCacheFileInfo(path, true);
				m = readMarkerList(target_file);
				cfi.fMarkers = (Reference<List<SVDBMarker>>)createRef(m);
				cfi.fMarkersRef = m;
			}
		}
		
		if (m == null) {
			m = new ArrayList<SVDBMarker>();
		}
		
		return m;
	}


	public boolean init(IProgressMonitor monitor, Object index_data) {
		boolean valid = false;
		fFileCache.clear();
		fBaseLocation = "";
		fIndexData = index_data;
		IDBReader rdr = allocReader();

		// Read the file list from the backing file
		try {
			RandomAccessFile in = null;
					
			in = fSVDBFS.openChannelRead("index");
			
			if (in != null) {
				
				rdr.init(in);
				fBaseLocation = rdr.readString();
				List<String> file_list = rdr.readStringList();
				List<Long> timestamp_list = rdr.readLongList();
				for (int i=0; i<file_list.size(); i++) {
					String path = file_list.get(i);
					CacheFileInfo cfi = getCacheFileInfo(path, true);
					cfi.fLastModified = timestamp_list.get(i);
				}
				
				fSVDBFS.closeChannel(in);
			}
			
			in = fSVDBFS.openChannelRead("index_data");
			if (in != null) {
				rdr.init(in);
				rdr.readObject(null, index_data.getClass(), index_data);
				debug("Cache " + fSVDBFS.getRoot() + " has base " + 
						((SVDBBaseIndexCacheData)index_data).getBaseLocation());
				fSVDBFS.closeChannel(in);
				valid = true;
			} else {
				debug("Failed to read index_data");
			}
//		} catch (IOException e) {}
		} catch (DBFormatException e) {
			  e.printStackTrace();
		} finally {
			freeReader(rdr);
		}
		
		return valid;
	}
	
	public void initLoad(IProgressMonitor monitor) {
		/**
		for (int i=0; i<fCacheSize && i<fFileList.size(); i++) {
			String path = fFileList.get(i);
			getPreProcFile(new NullProgressMonitor(), path);
			getFileTree(new NullProgressMonitor(), path);
			getFile(new NullProgressMonitor(), path);
		}
		 */
	}

	public Set<String> getFileList() {
		return fFileCache.keySet();
	}
	
	public long getLastModified(String path) {
		CacheFileInfo cfi = getCacheFileInfo(path, false);
		
		if (cfi != null) {
			return cfi.fLastModified;
		} else {
			System.out.println("File \"" + path + "\" not in cache");
		}
		return -1;
	}
	
	public void setLastModified(String path, long timestamp) {
		if (timestamp == -1) {
			try {
				throw new Exception();
			} catch (Exception e) {
				System.out.println("NEG timestamp");
				e.printStackTrace();
			}
		}
		CacheFileInfo cfi = getCacheFileInfo(path, true);
		cfi.fLastModified = timestamp;
	}

	public SVDBFile getPreProcFile(IProgressMonitor monitor, String path) {
		CacheFileInfo cfi = getCacheFileInfo(path, false);
		SVDBFile pp_file = (cfi != null)?cfi.fSVDBPreProcFile.get():null;
		
		if (pp_file == null) {
			String target_dir = computePathDir(path);
			
			if (fSVDBFS.fileExists(target_dir + "/preProcFile")) {
				cfi = getCacheFileInfo(path, true);
				RandomAccessFile in = fSVDBFS.openChannelRead(target_dir + "/preProcFile"); 
				pp_file = readFile(in, path);
				fSVDBFS.closeChannel(in);
				cfi.fSVDBPreProcFile = (Reference<SVDBFile>)createRef(pp_file);
				cfi.fSVDBPreProcFileRef = pp_file;
			}
		}
		
		return pp_file;
	}

	public SVDBFile getFile(IProgressMonitor monitor, String path) {
		CacheFileInfo cfi = getCacheFileInfo(path, false);

		SVDBFile file = (cfi != null)?cfi.fSVDBFile.get():null;
		
		if (file == null) {
			String target_dir = computePathDir(path);
			
			if (fSVDBFS.fileExists(target_dir + "/file")) {
				cfi = getCacheFileInfo(path, true);
				RandomAccessFile in = fSVDBFS.openChannelRead(target_dir + "/file");
				file = readFile(in, path);
				fSVDBFS.closeChannel(in);
				cfi.fSVDBFile = (Reference<SVDBFile>)createRef(file);
				cfi.fSVDBFileRef = file;
				fNumFilesRead++;
			} else {
				debug("Target dir does not exist: " + target_dir);
			}
		}
		
		return file;
	}

	public void setPreProcFile(String path, SVDBFile file) {
		if (file == null) {
			try {
				throw new Exception("SVDBFile for path \"" + path + "\" is null");
			} catch (Exception e) {
				fLog.error("SVDBFile for path \"" + path + "\" is null", e);
			}
		}

		CacheFileInfo cfi = getCacheFileInfo(path, true);

		cfi.fSVDBPreProcFile = (Reference<SVDBFile>)createRef(file);
		cfi.fSVDBPreProcFileRef = file;
		
		// TODO: write-through to the cache
		// writeBackPreProcFile(path, file);
		
	}

	public void setFile(String path, SVDBFile file) {
		CacheFileInfo cfi = getCacheFileInfo(path, true);
		
		if (file == null) {
			debug("setFile \"" + path + "\" == NULL");
			// TODO: should actually remove?
			cfi.fSVDBFile = new WeakReference<SVDBFile>(null);
			String target_dir = computePathDir(path);
			fSVDBFS.delete(target_dir + "/file");
		} else {
			cfi.fSVDBFile = (Reference<SVDBFile>)createRef(file);
			cfi.fSVDBFileRef = file;

			// TODO:
			// writeBackFile(path, file);
		}
	}

	public void setFileTree(String path, SVDBFileTree file_tree) {
		CacheFileInfo cfi = getCacheFileInfo(path, true);
		cfi.fSVDBFileTree = (Reference<SVDBFileTree>)createRef(file_tree);
		cfi.fSVDBFileTreeRef = file_tree;
		
		if (path == null) {
			System.out.println("Null path");
		}

		// TODO:
		// writeBackFileTree(path, file_tree);
	}
	
	public SVDBFileTree getFileTree(IProgressMonitor monitor, String path) {
		CacheFileInfo cfi = getCacheFileInfo(path, false);
		
		SVDBFileTree ft = (cfi != null)?cfi.fSVDBFileTree.get():null;
		
		if (ft == null) {
			String target_dir = computePathDir(path);
			
			if (fSVDBFS.fileExists(target_dir + "/fileTreeMap")) {
				cfi = getCacheFileInfo(path, true);
				RandomAccessFile in = fSVDBFS.openChannelRead(target_dir + "/fileTreeMap"); 
				ft = readFileTree(in);
				fSVDBFS.closeChannel(in);

				cfi.fSVDBFileTree = (Reference<SVDBFileTree>)createRef(ft);
				cfi.fSVDBFileTreeRef = ft;
			} else {
				fLog.debug("FileTree path " + path + " doesn't exist");
			}
		}
		
		return ft;
	}
	

	public void removeFile(String path) {
		CacheFileInfo file = fFileCache.get(path);
		fFileCache.remove(path);
		
		// Remove from linked list
		removeElement(file);
		
		String target_dir = computePathDir(path);

		// remove backing cache, if it exists
		fSVDBFS.delete(target_dir);
	}
	
	private String computePathDir(String path) {
		/*
		String ret = path;
		ret = ret.replace('/', '_');
		ret = ret.replace('$', '_');
		ret = ret.replace('{', '_');
		ret = ret.replace('}', '_');

		return ret;
		 */
		return SVFileUtils.computeMD5(path);
	}
	
	private SVDBFile readFile(RandomAccessFile in, String path) {
		IDBReader reader = allocReader();
		reader.init(in);
		
		SVDBFile ret = new SVDBFile();
		try {
			reader.readObject(null, ret.getClass(), ret);
		} catch (DBFormatException e) {
			e.printStackTrace();
		} finally {
			freeReader(reader);
		}

		return ret;
	}

	private SVDBFileTree readFileTree(RandomAccessFile in) {
		IDBReader reader = allocReader();
		reader.init(in);
		
		SVDBFileTree ret = new SVDBFileTree();
		try {
			reader.readObject(null, ret.getClass(), ret);
		} catch (DBFormatException e) {
			e.printStackTrace();
		} finally {
			freeReader(reader);
		}
		
		return ret;
	}
	
	private List<SVDBMarker> readMarkerList(String path) {
		RandomAccessFile in = fSVDBFS.openChannelRead(path);
		IDBReader reader = allocReader();
		reader.init(in);
		
		List<SVDBMarker> ret = null;
		
		try {
			ret = (List<SVDBMarker>)reader.readItemList(null);
		} catch (DBFormatException e) {
			e.printStackTrace();
		} finally {
			freeReader(reader);
		}

		fSVDBFS.closeChannel(in);
		
		return ret;
	}
	
	public void sync() {
		IDBWriter writer = allocWriter();
		
		// Writeback any remaining cached files
		while (fCacheHead != null) {
			removeElement(fCacheHead);
		}
		
		// Wait for the write-back jobs to complete
		while (true) {
			IJob j = null;
			synchronized (fWritebackJobs) {
				if (fWritebackJobs.size() > 0) {
					j = fWritebackJobs.remove(0);
				}
			}
			if (j == null) {
				break;
			}
		}
		
		try {
			RandomAccessFile out = fSVDBFS.openChannelWrite("index");
			if (out == null) {
				throw new DBWriteException("Failed to open file \"index\" for writing");
			}
			writer.init(out);
			writer.writeString(fBaseLocation);
			List<String> tmp = new ArrayList<String>();
			tmp.addAll(fFileCache.keySet());
			writer.writeStringList(tmp);
			List<Long> timestamp_list = new ArrayList<Long>();
			for (String path : fFileCache.keySet()) {
				CacheFileInfo cfi = getCacheFileInfo(path, true);
				timestamp_list.add(cfi.fLastModified);
			}
			writer.writeLongList(timestamp_list);
			
			writer.close();
			fSVDBFS.closeChannel(out);
			
			out = fSVDBFS.openChannelWrite("index_data");
			writer.init(out);
			writer.writeObject(fIndexData.getClass(), fIndexData);
			writer.close();
			fSVDBFS.closeChannel(out);
		} catch (DBWriteException e) {
			e.printStackTrace();
		} finally {
			freeWriter(writer);
		}
	}
	
	private IDBReader allocReader() {
		IDBReader reader = null;
		synchronized (fPersistenceRdrSet) {
			if (fPersistenceRdrSet.size() > 0) {
				reader = fPersistenceRdrSet.remove(fPersistenceRdrSet.size()-1);
			}
		}
		if (reader == null) {
			reader = new SVDBPersistenceRW();
		}
		
		return reader;
	}
	
	private void freeReader(IDBReader reader) {
		synchronized (fPersistenceRdrSet) {
			fPersistenceRdrSet.add(reader);
		}
	}
	
	private IDBWriter allocWriter() {
		IDBWriter writer = null;
		synchronized (fPersistenceWriterSet) {
			if (fPersistenceWriterSet.size() > 0) {
				writer = fPersistenceWriterSet.remove(fPersistenceWriterSet.size()-1);
			}
		}
		if (writer == null) {
			writer = new SVDBPersistenceRW();
		}
		return writer;
	}
	
	private void freeWriter(IDBWriter writer) {
		synchronized (fPersistenceWriterSet) {
			fPersistenceWriterSet.add(writer);
		}
	}
	
	private void writeBackPreProcFile(CacheFileInfo info, String path, SVDBFile file) {
		
		String target_dir = computePathDir(path);
		String file_path = target_dir + "/preProcFile";
	
		IJobMgr job_mgr = SVCorePlugin.getJobMgr();
		IJob job = job_mgr.createJob();
		job.init("WriteBackPreProcFile", 
				new WriteBackFileRunnable(job, info, target_dir, file_path, file));
		job.setPriority(1);
		synchronized (fWritebackJobs) {
			fWritebackJobs.add(job);
		}
		job_mgr.queueJob(job);
	}

	private void writeBackFile(CacheFileInfo info, String path, SVDBFile file) {
		String target_dir = computePathDir(path);
		String file_path = target_dir + "/file";

		IJobMgr job_mgr = SVCorePlugin.getJobMgr();
		IJob job = job_mgr.createJob();
		job.init("WriteBackFile", 
				new WriteBackFileRunnable(job, info, target_dir, file_path, file));
		job.setPriority(1);
		synchronized (fWritebackJobs) {
			fWritebackJobs.add(job);
		}
		job_mgr.queueJob(job);
	}
	
	private void writeBackFileTree(CacheFileInfo info, String path, SVDBFileTree file_tree) {
		String target_dir = computePathDir(path);
		String file_path = target_dir + "/fileTreeMap";

		IJobMgr job_mgr = SVCorePlugin.getJobMgr();
		IJob job = job_mgr.createJob();
		job.init("WriteBackFile", 
				new WriteBackFileTreeRunnable(job, info, target_dir, file_path, file_tree));
		job.setPriority(1);
		synchronized (fWritebackJobs) {
			fWritebackJobs.add(job);
		}
		job_mgr.queueJob(job);
	}
	
	private void writeBackMarkerList(CacheFileInfo info, String path, List<SVDBMarker> markers) {
		String target_dir = computePathDir(path);
		String file_path  = target_dir + "/markers";

		IJobMgr job_mgr = SVCorePlugin.getJobMgr();
		IJob job = job_mgr.createJob();
		job.init("WriteBackMarkerList", 
				new WriteBackMarkerListRunnable(job, info, target_dir, file_path, markers));
		job.setPriority(1);
		synchronized (fWritebackJobs) {
			fWritebackJobs.add(job);
		}
		job_mgr.queueJob(job);
	}

	private class WriteBackFileRunnable implements Runnable {
		private IJob				fJob;
		private CacheFileInfo		fInfo;
		private String				fTargetDir;
		private String				fFilePath;
		private SVDBFile			fFile;
		
		public WriteBackFileRunnable(IJob job, CacheFileInfo info, String target_dir, String file_path, SVDBFile file) {
			fJob = job;
			fInfo = info;
			fTargetDir = target_dir;
			fFilePath = file_path;
			fFile = file;
		}
		
		public void run() {
			IDBWriter writer = allocWriter();
			
			fSVDBFS.mkdirs(fTargetDir);
			try {
				RandomAccessFile out = fSVDBFS.openChannelWrite(fFilePath);
				
				writer.init(out);
				writer.writeObject(fFile.getClass(), fFile);
				writer.close();
				fSVDBFS.closeChannel(out);
			} catch (DBWriteException e) {
				e.printStackTrace();
			} finally {
				freeWriter(writer);
				// Remove reference to allow storage to be collected
				fInfo.fSVDBFileRef = null;
				synchronized (fWritebackJobs) {
					fWritebackJobs.remove(fJob);
				}
			}
		}
	}

	private class WriteBackFileTreeRunnable implements Runnable {
		private IJob				fJob;
		private CacheFileInfo		fInfo;
		private String				fTargetDir;
		private String				fFilePath;
		private SVDBFileTree		fFileTree;
		
		public WriteBackFileTreeRunnable(IJob job, CacheFileInfo info, String target_dir, String file_path, SVDBFileTree ft) {
			fJob = job;
			fInfo = info;
			fTargetDir = target_dir;
			fFilePath = file_path;
			fFileTree = ft;
		}
		
		public void run() {
			fSVDBFS.mkdirs(fTargetDir);
			
			IDBWriter writer = allocWriter();
			
			try {
				RandomAccessFile out = fSVDBFS.openChannelWrite(fFilePath);
				writer.init(out);
				synchronized (fFileTree) {
					writer.writeObject(fFileTree.getClass(), fFileTree);
				}
				writer.close();
				out.close();
			} catch (Exception e) {
				e.printStackTrace();
			} finally {
				freeWriter(writer);
				fInfo.fSVDBFileTreeRef = null;
				synchronized (fWritebackJobs) {
					fWritebackJobs.remove(fJob);
				}
			}
		}
	}
	
	private class WriteBackMarkerListRunnable implements Runnable {
		private IJob					fJob;
		private CacheFileInfo			fInfo;
		private String					fTargetDir;
		private String					fFilePath;
		private List<SVDBMarker>		fMarkers;
	
		public WriteBackMarkerListRunnable(IJob job, CacheFileInfo info, String target_dir, String file_path, List<SVDBMarker> markers) {
			fJob = job;
			fInfo = info;
			fTargetDir = target_dir;
			fFilePath = file_path;
			fMarkers = markers;
		}
		
		public void run() {
			fSVDBFS.mkdirs(fTargetDir);

			IDBWriter writer = allocWriter();
			try {
				RandomAccessFile out = fSVDBFS.openChannelWrite(fFilePath);
				writer.init(out);
				writer.writeItemList(fMarkers);
				writer.close();
				fSVDBFS.closeChannel(out);
			} catch (DBWriteException e) {
				e.printStackTrace();
			} finally {
				freeWriter(writer);
				fInfo.fMarkersRef = null;
				synchronized (fWritebackJobs) {
					fWritebackJobs.remove(fJob);
				}
			}
		}
	}
	
	private Reference createRef(Object obj) {
		if (fUseSoftRef) {
			return new SoftReference(obj);
		} else {
			return new WeakReference(obj);
		}
	}
	
	private void debug(String msg) {
		// TODO:
	}

	private void addElementToTail(CacheFileInfo info) {
		synchronized (SVDBThreadedFileIndexCache.class) {
			// Add references
			info.fCached = true;
			info.fSVDBFileRef = info.fSVDBFile.get();
			info.fSVDBFileTreeRef = info.fSVDBFileTree.get();
			info.fSVDBPreProcFileRef = info.fSVDBPreProcFile.get();
			
			if (fCacheHead == null) {
				// First entry
				fCacheHead = info;
				fCacheTail = info;
				info.fPrev = null;
				info.fNext = null;
			} else {
				// Add the new file info to the linked list
				fCacheTail.fNext = info;
				info.fPrev = fCacheTail;
				fCacheTail = info;
				info.fNext = null;
			}
			fCacheSize++;
			while (fCacheSize > fMaxCacheSize) {
				// Remove a few entries
				removeElement(fCacheHead);
			}
		}
	}
	
	private void moveElementToTail(CacheFileInfo info) {
		synchronized (SVDBThreadedFileIndexCache.class) {
			if (fCacheTail != info) {
				if (info.fPrev == null) {
					fCacheHead = info.fNext;
				} else {
					info.fPrev.fNext = info.fNext;
				}

				if (info.fNext == null) {
					fCacheTail = info.fPrev;
				} else {
					info.fNext.fPrev = info.fPrev;
				}

				if (fCacheHead == null) {
					// First entry
					fCacheHead = info;
					fCacheTail = info;
					info.fPrev = null;
					info.fNext = null;
				} else {
					// Add the file info to the linked list
					fCacheTail.fNext = info;
					info.fPrev = fCacheTail;
					fCacheTail = info;
					info.fNext = null;
				}
			}
		}
	}
	
	private void removeElement(CacheFileInfo info) {
		synchronized (SVDBThreadedFileIndexCache.class) {
			if (info.fPrev == null) {
				fCacheHead = info.fNext;
			} else {
				info.fPrev.fNext = info.fNext;
			}

			if (info.fNext == null) {
				fCacheTail = info.fPrev;
			} else {
				info.fNext.fPrev = info.fPrev;
			}
			
			// Writeback cached items
			if (info.fSVDBFileRef != null) {
				writeBackFile(info, info.fPath, info.fSVDBFileRef);
			}
			if (info.fSVDBFileTreeRef != null) {
				writeBackFileTree(info, info.fPath, info.fSVDBFileTreeRef);
				
			}
			if (info.fSVDBPreProcFileRef != null) {
				writeBackPreProcFile(info, info.fPath, info.fSVDBPreProcFileRef);
				
			}
			if (info.fMarkers != null) {
				writeBackMarkerList(info, info.fPath, info.fMarkersRef);
			}
			info.fCached = false;
			fCacheSize--;
		}
	}
}

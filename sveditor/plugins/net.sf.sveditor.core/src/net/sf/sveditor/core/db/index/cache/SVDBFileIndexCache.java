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

import java.io.DataInput;
import java.io.DataOutput;
import java.io.File;
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
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;

@SuppressWarnings({"rawtypes","unchecked"})
public class SVDBFileIndexCache implements ISVDBIndexCache, ILogLevelListener {
	private String							fBaseLocation;
	private Map<String, CacheFileInfo>		fFileCache;
	private ISVDBFS							fSVDBFS;
	private Object							fIndexData;
	private LogHandle						fLog;
	private List<IDBReader>					fPersistenceRdrSet;
	private List<IDBWriter>					fPersistenceWriterSet;
	private long							fNumFilesRead = 0;
	private boolean						fDebugEn = false;

	private int							fNumWriteBackThreads = 0;
	private Thread							fWriteBackThread[];
	private List<WriteBackInfo>				fWriteBackQueue;
	
	private int							fMaxCacheSize = 100;
	
	private static CacheFileInfo			fCacheHead;
	private static CacheFileInfo			fCacheTail;
	private static int					fCacheSize;
	
	private boolean						fUseSoftRef = true;

	final class CacheFileInfo {
		public boolean						fCached;
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
		
		public CacheFileInfo() {
			fSVDBPreProcFile = (Reference<SVDBFile>)createRef(null);
			fSVDBFileTree = (Reference<SVDBFileTree>)createRef(null);
			fSVDBFile = (Reference<SVDBFile>)createRef(null);
			fMarkers = (Reference<List<SVDBMarker>>)createRef(null);
			fLastModified = -1;
		}
	}
	
	final class WriteBackInfo {
		public static final int SVDB_FILE=0, SVDB_FILE_TREE=1, MARKERS=2;
		public int							fType;
		public SVDBFile						fFile;
		public SVDBFileTree					fFileTree;
		public List<SVDBMarker>				fMarkers;
		public String						fFilePath;
		public String						fTargetDir;
		public WriteBackInfo(String target_dir, String file_path, SVDBFile file) {
			fTargetDir = target_dir;
			fFilePath = file_path;
			fFile = file;
			fType = SVDB_FILE;
		}
		public WriteBackInfo(String target_dir, String file_path, SVDBFileTree file) {
			fTargetDir = target_dir;
			fFilePath = file_path;
			fFileTree = file;
			fType = SVDB_FILE_TREE;
		}
		public WriteBackInfo(String target_dir, String file_path, List<SVDBMarker> markers) {
			fTargetDir = target_dir;
			fFilePath = file_path;
			fMarkers = markers;
			fType = MARKERS;
		}
	}
	
	public SVDBFileIndexCache(ISVDBFS fs) {
		fSVDBFS = fs;
		fFileCache = new HashMap<String, SVDBFileIndexCache.CacheFileInfo>();
		fLog = LogFactory.getLogHandle("SVDBFileIndexCache");
		fDebugEn = fLog.isEnabled();
		fLog.addLogLevelListener(this);
		fPersistenceRdrSet = new ArrayList<IDBReader>(); 
		fPersistenceWriterSet = new ArrayList<IDBWriter>();
		fWriteBackQueue = new ArrayList<SVDBFileIndexCache.WriteBackInfo>();
		
		fNumWriteBackThreads = SVCorePlugin.getNumIndexCacheThreads();
		
		if (fNumWriteBackThreads > 0) {
			fWriteBackThread = new Thread[fNumWriteBackThreads];
			for (int i=0; i<fWriteBackThread.length; i++) {
				fWriteBackThread[i] = new Thread(new Runnable() {
					public void run() {
						writeBackWorker();
					}
				}, "WriteBackWorker" + i);
				fWriteBackThread[i].setPriority(Thread.MIN_PRIORITY);
				fWriteBackThread[i].start();
			}
		}
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
			fLog.debug(LEVEL_MID, "Clear Index Cache");
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
					file = new CacheFileInfo();
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
		
		writeBackMarkerList(path, markers);
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
			DataInput in = fSVDBFS.openDataInput("index");
				
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

				fSVDBFS.closeInput(in);
			}
		
			in = fSVDBFS.openDataInput("index_data");
			if (in != null) {
				rdr.init(in);
				rdr.readObject(null, index_data.getClass(), index_data);
				if (fDebugEn) {
					fLog.debug(LEVEL_MIN, "Cache " + fSVDBFS.getRoot() + " has base " + 
							((SVDBBaseIndexCacheData)index_data).getBaseLocation());
				}
				fSVDBFS.closeInput(in);
				valid = true;
			} else {
				if (fDebugEn) {
					fLog.debug(LEVEL_MIN, "Failed to read index_data");
				}
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
				DataInput in = fSVDBFS.openDataInput(target_dir + "/preProcFile"); 
				pp_file = readFile(in, path);
				fSVDBFS.closeInput(in);
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
				DataInput in = fSVDBFS.openDataInput(target_dir + "/file");
				file = readFile(in, path);
				fSVDBFS.closeInput(in);
				cfi.fSVDBFile = (Reference<SVDBFile>)createRef(file);
				cfi.fSVDBFileRef = file;
				fNumFilesRead++;
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
		
		// write-through to the cache
		writeBackPreProcFile(path, file);
		
	}

	public void setFile(String path, SVDBFile file) {
		CacheFileInfo cfi = getCacheFileInfo(path, true);
		
		if (file == null) {
			if (fDebugEn) {
				fLog.debug(LEVEL_MAX, "setFile \"" + path + "\" == NULL");
			}
			// TODO: should actually remove?
			cfi.fSVDBFile = new WeakReference<SVDBFile>(null);
			String target_dir = computePathDir(path);
			fSVDBFS.delete(target_dir + "/file");
		} else {
			cfi.fSVDBFile = (Reference<SVDBFile>)createRef(file);
			cfi.fSVDBFileRef = file;

			writeBackFile(path, file);
		}
	}

	public void setFileTree(String path, SVDBFileTree file_tree) {
		CacheFileInfo cfi = getCacheFileInfo(path, true);
		cfi.fSVDBFileTree = (Reference<SVDBFileTree>)createRef(file_tree);
		cfi.fSVDBFileTreeRef = file_tree;
		
		if (path == null) {
			System.out.println("Null path");
		}

		writeBackFileTree(path, file_tree);
	}
	
	public SVDBFileTree getFileTree(IProgressMonitor monitor, String path) {
		CacheFileInfo cfi = getCacheFileInfo(path, false);
		
		SVDBFileTree ft = (cfi != null)?cfi.fSVDBFileTree.get():null;
		
		if (ft == null) {
			String target_dir = computePathDir(path);
			
			if (fSVDBFS.fileExists(target_dir + "/fileTreeMap")) {
				cfi = getCacheFileInfo(path, true);
				DataInput in = fSVDBFS.openDataInput(target_dir + "/fileTreeMap"); 
				ft = readFileTree(in);
				fSVDBFS.closeInput(in);

				cfi.fSVDBFileTree = (Reference<SVDBFileTree>)createRef(ft);
				cfi.fSVDBFileTreeRef = ft;
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
	
	private SVDBFile readFile(DataInput in, String path) {
//		debug("readFile " + path);
//		System.out.println("readFile: " + path);
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

	private SVDBFileTree readFileTree(DataInput in) {
//		debug("readFileTree");
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
		DataInput in = fSVDBFS.openDataInput(path);
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

		fSVDBFS.closeInput(in);
		
		return ret;
	}
	
	public void sync() {
		IDBWriter writer = allocWriter();
		
		// Wait for the write-back jobs to complete
		while (true) {
			synchronized (fWriteBackQueue) {
				if (fWriteBackQueue.size() == 0) {
					break;
				}
				try {
					fWriteBackQueue.wait(100);
				} catch (InterruptedException e) {
					break;
				}
			}
		}
		
		try {
			DataOutput out = fSVDBFS.openDataOutput("index");
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
			fSVDBFS.closeOutput(out);
			
			out = fSVDBFS.openDataOutput("index_data");
			writer.init(out);
			writer.writeObject(fIndexData.getClass(), fIndexData);
			writer.close();
			fSVDBFS.closeOutput(out);
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
	
	private void writeBackPreProcFile(String path, SVDBFile file) {
		
		String target_dir = computePathDir(path);
		String file_path = target_dir + "/preProcFile";
	
		if (fNumWriteBackThreads > 0) {
			WriteBackInfo info = new WriteBackInfo(target_dir, file_path, file);
			synchronized (fWriteBackQueue) {
				// First, go through and look for any duplicates
				for (int i=0; i<fWriteBackQueue.size(); i++) {
					if (fWriteBackQueue.get(i).fType == WriteBackInfo.SVDB_FILE &&
							fWriteBackQueue.get(i).fTargetDir.equals(target_dir) &&
							fWriteBackQueue.get(i).fFilePath.equals(file_path)) {
						fWriteBackQueue.remove(i);
						i--;
					}
				}
				fWriteBackQueue.add(info);
				fWriteBackQueue.notify();
			}
		} else {
			writeBackFileWorker(target_dir, file_path, file);
		}
	}

	private void writeBackFile(String path, SVDBFile file) {
		String target_dir = computePathDir(path);
		String file_path = target_dir + "/file";
		
		if (fNumWriteBackThreads > 0) {
			WriteBackInfo info = new WriteBackInfo(target_dir, file_path, file);
			synchronized (fWriteBackQueue) {
				fWriteBackQueue.add(info);
				fWriteBackQueue.notify();
			}
		} else {
			writeBackFileWorker(target_dir, file_path, file);
		}
	}
	
	private void writeBackFileTree(String path, SVDBFileTree file_tree) {
		String target_dir = computePathDir(path);
		String file_path = target_dir + "/fileTreeMap";

		if (fNumWriteBackThreads > 0) {
			WriteBackInfo info = new WriteBackInfo(target_dir, file_path, file_tree);
			synchronized (fWriteBackQueue) {
				// First, go through and look for any duplicates
				for (int i=0; i<fWriteBackQueue.size(); i++) {
					if (fWriteBackQueue.get(i).fType == WriteBackInfo.SVDB_FILE_TREE &&
							fWriteBackQueue.get(i).fTargetDir.equals(target_dir) &&
							fWriteBackQueue.get(i).fFilePath.equals(file_path)) {
						fWriteBackQueue.remove(i);
						i--;
					}
				}
				fWriteBackQueue.add(info);
				fWriteBackQueue.notify();
			}
		} else {
			writeBackFileTreeWorker(target_dir, file_path, file_tree);
		}
	}
	
	private void writeBackMarkerList(String path, List<SVDBMarker> markers) {
		String target_dir = computePathDir(path);
		String file_path  = target_dir + "/markers";

		if (fNumWriteBackThreads > 0) {
			WriteBackInfo info = new WriteBackInfo(target_dir, file_path, markers);
			synchronized (fWriteBackQueue) {
				fWriteBackQueue.add(info);
				fWriteBackQueue.notify();
			}
		} else {
			writeBackMarkerListWorker(target_dir, file_path, markers);
		}
	}

	private void writeBackWorker() {
		while (true) {
			WriteBackInfo info = null;
			
			synchronized (fWriteBackQueue) {
				while (fWriteBackQueue.size() == 0) {
					try {
						fWriteBackQueue.wait();
					} catch (InterruptedException e) {}
				}
				if (fWriteBackQueue.size() > 0) {
					info = fWriteBackQueue.remove(fWriteBackQueue.size()-1);
				}
			}
			
			if (info != null) {
				switch (info.fType) {
					case WriteBackInfo.SVDB_FILE:
//						System.out.println("WriteBack " + info.fFile.getFilePath());
						writeBackFileWorker(info.fTargetDir, info.fFilePath, info.fFile);
						break;
					case WriteBackInfo.SVDB_FILE_TREE:
//						System.out.println("WriteBack " + info.fFileTree.getFilePath());
						writeBackFileTreeWorker(info.fTargetDir, info.fFilePath, info.fFileTree);
						break;
					case WriteBackInfo.MARKERS:
//						System.out.println("WriteBack markers");
						writeBackMarkerListWorker(info.fTargetDir, info.fFilePath, info.fMarkers);
						break;
				}
			}
		}
	}

	private void writeBackFileWorker(String target_dir, String file_path, SVDBFile file) {
		IDBWriter writer = allocWriter();
		
		fSVDBFS.mkdirs(target_dir);
		try {
			DataOutput out = fSVDBFS.openDataOutput(file_path);
			
			writer.init(out);
			writer.writeObject(file.getClass(), file);
			writer.close();
			fSVDBFS.closeOutput(out);
		} catch (DBWriteException e) {
			e.printStackTrace();
		} finally {
			freeWriter(writer);
		}
	}

	private void writeBackFileTreeWorker(String target_dir, String file_path, SVDBFileTree file_tree) {
		fSVDBFS.mkdirs(target_dir);
		
		IDBWriter writer = allocWriter();
		
		try {
			DataOutput out = fSVDBFS.openDataOutput(file_path);
			writer.init(out);
			synchronized (file_tree) {
				writer.writeObject(file_tree.getClass(), file_tree);
			}
			writer.close();
			fSVDBFS.closeOutput(out);
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			freeWriter(writer);
		}
	}
	
	private void writeBackMarkerListWorker(String target_dir, String file_path, List<SVDBMarker> markers) {
		fSVDBFS.mkdirs(target_dir);

		IDBWriter writer = allocWriter();
		try {
			DataOutput out = fSVDBFS.openDataOutput(file_path);
			writer.init(out);
			writer.writeItemList(markers);
			writer.close();
			fSVDBFS.closeOutput(out);
		} catch (DBWriteException e) {
			e.printStackTrace();
		} finally {
			freeWriter(writer);
		}
	}

	private Reference createRef(Object obj) {
		if (fUseSoftRef) {
			return new SoftReference(obj);
		} else {
			return new WeakReference(obj);
		}
	}
	
	private void addElementToTail(CacheFileInfo info) {
		synchronized (SVDBFileIndexCache.class) {
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
		synchronized (SVDBFileIndexCache.class) {
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
		synchronized (SVDBFileIndexCache.class) {
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
			
			// Release references
			info.fSVDBFileRef = null;
			info.fSVDBFileTreeRef = null;
			info.fSVDBPreProcFileRef = null;
			info.fCached = false;
			fCacheSize--;
		}
	}
}

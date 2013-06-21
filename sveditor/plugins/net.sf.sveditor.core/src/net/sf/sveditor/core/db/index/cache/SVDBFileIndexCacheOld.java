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

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
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
import org.eclipse.core.runtime.NullProgressMonitor;

@SuppressWarnings({"rawtypes","unchecked"})
public class SVDBFileIndexCacheOld implements ISVDBIndexCache, ILogLevelListener {
	private String							fBaseLocation;
	private String							fBaseLocationInfo;
	private Map<String, CacheFileInfo>		fFileCache;
	private Map<String, CacheFileInfo>		fArgFileCache;
	private ISVDBFS							fSVDBFS;
	private Object							fIndexData;
	private LogHandle						fLog;
	private List<IDBReader>					fPersistenceRdrSet;
	private List<IDBWriter>					fPersistenceWriterSet;
	private long							fNumFilesRead = 0;
	private boolean							fDebugEn = false;

	private int								fMaxCacheSize = 100;
	
	private static CacheFileInfo			fCacheHead;
	private static CacheFileInfo			fCacheTail;
	private static int						fCacheSize;
	
	private boolean							fUseSoftRef = true;

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
		public long							fLastModified;
		
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
	
	public SVDBFileIndexCacheOld(ISVDBFS fs) {
		fSVDBFS = fs;
		fFileCache = new HashMap<String, SVDBFileIndexCacheOld.CacheFileInfo>();
		fArgFileCache = new HashMap<String, SVDBFileIndexCacheOld.CacheFileInfo>();
		fLog = LogFactory.getLogHandle("SVDBFileIndexCache");
		fDebugEn = fLog.isEnabled();
		fLog.addLogLevelListener(this);
		fPersistenceRdrSet = new ArrayList<IDBReader>(); 
		fPersistenceWriterSet = new ArrayList<IDBWriter>();
	}
	
	public ISVDBIndexCacheMgr getCacheMgr() {
		// TODO:
		return null;
	}

	public void dispose() { 
		clear(new NullProgressMonitor());
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

	public void clear(IProgressMonitor monitor) {
		// Delete entire index
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Clear Index Cache " + fBaseLocationInfo);
		}
		fFileCache.clear();
		fArgFileCache.clear();
		fSVDBFS.delete(monitor, "");
	}

	public void addFile(String path, boolean is_argfile) {
		if (is_argfile) {
			getArgFileCacheFileInfo(path, false);
		} else {
			getCacheFileInfo(path, true);
		}
	}
	
	private CacheFileInfo getCacheFileInfo(String path, boolean create) {
		if (fDebugEn) {
			fLog.debug("getCacheFileInfo: " + path + " " + create);

			if (create && path.endsWith(".f")) {
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
			/*
			 */
		}
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

	private CacheFileInfo getArgFileCacheFileInfo(String path, boolean create) {
		synchronized (fArgFileCache) {
			CacheFileInfo file = null;
			if (!fArgFileCache.containsKey(path)) {
				if (create) {
					file = new CacheFileInfo();
					fArgFileCache.put(path, file);
				}
			} else {
				file = fArgFileCache.get(path);
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
	
	public void setMarkers(String path, List<SVDBMarker> markers, boolean is_argfile) {
		CacheFileInfo cfi;
		
		if (is_argfile) {
			cfi = getArgFileCacheFileInfo(path, true);
		} else {
			cfi = getCacheFileInfo(path, true);
		}
		
		if (fDebugEn) {
			fLog.debug("setMarkers: " + path + " (" + markers.size() + ")");
		}

		cfi.fMarkers = (Reference<List<SVDBMarker>>)createRef(markers);
		
		// We know we're referenced, so update the links
		cfi.fMarkersRef = markers;
		
		writeBackMarkerList(path, markers);
	}
	
	public List<SVDBMarker> getMarkers(String path) {
		CacheFileInfo cfi;
		
		if ((cfi = getCacheFileInfo(path, false)) == null) {
			cfi = getArgFileCacheFileInfo(path, false);
		}
		
		List<SVDBMarker> m = (cfi != null)?cfi.fMarkers.get():null;
		
		if (m == null) {
			String parent_dir = computePathDir(path);
			String target_file = parent_dir + "/markers";
			if (fSVDBFS.fileExists(target_file)) {
				if (fSVDBFS.fileExists(parent_dir + "/argfile")) {
					cfi = getArgFileCacheFileInfo(path, true);
				} else {
					cfi = getCacheFileInfo(path, true);
				}
				m = readMarkerList(target_file);
				cfi.fMarkers = (Reference<List<SVDBMarker>>)createRef(m);
				cfi.fMarkersRef = m;
			}
		}
		
		if (fDebugEn) {
			fLog.debug("setMarkers: " + path + " (" + ((m == null)?"null":m.size()) + ")");
		}
	
		/*
		if (m == null) {
			m = new ArrayList<SVDBMarker>();
		}
		 */
		
		return m;
	}


	public boolean init(IProgressMonitor monitor, Object index_data, String base_location) {
		boolean valid = false;
		fFileCache.clear();
		fArgFileCache.clear();
		fBaseLocationInfo = base_location;
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
				List<String> arg_file_list = rdr.readStringList();
				List<Long> timestamp_list = rdr.readLongList();
				List<Long> arg_timestamp_list = rdr.readLongList();
				for (int i=0; i<file_list.size(); i++) {
					String path = file_list.get(i);
					CacheFileInfo cfi = getCacheFileInfo(path, true);
					cfi.fLastModified = timestamp_list.get(i);
				}
				
				for (int i=0; i<arg_file_list.size(); i++) {
					String path = arg_file_list.get(i);
					CacheFileInfo cfi = getArgFileCacheFileInfo(path, true);
					cfi.fLastModified = arg_timestamp_list.get(i);
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
	
	public synchronized Set<String> getFileList(boolean is_argfile) {
		if (fDebugEn) {
			fLog.debug("--> getFileList: " + is_argfile);
		}
		Set<String> ret;
		if (is_argfile) {
			ret = fArgFileCache.keySet();
		} else {
			ret = fFileCache.keySet();
		}
		if (fDebugEn) {
			for (String p : ret) {
				fLog.debug("  path: " + p);
			}
			fLog.debug("<-- getFileList: " + is_argfile);
		}
		return ret;
	}
	
	public long getLastModified(String path) {
		CacheFileInfo cfi;
		
		if ((cfi = getCacheFileInfo(path, false)) == null) {
			cfi = getArgFileCacheFileInfo(path, false);
		}
		
		if (cfi != null) {
			return cfi.fLastModified;
		} else {
			System.out.println("File \"" + path + "\" not in cache");
		}
		return -1;
	}
	
	public void setLastModified(String path, long timestamp, boolean is_argfile) {
		if (timestamp == -1) {
			try {
				throw new Exception();
			} catch (Exception e) {
				System.out.println("NEG timestamp");
				e.printStackTrace();
			}
		}
		CacheFileInfo cfi;
		
		if (is_argfile) {
			cfi = getArgFileCacheFileInfo(path, true);
		} else {
			cfi = getCacheFileInfo(path, true);
		}
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
		CacheFileInfo cfi;
		
		if ((cfi = getCacheFileInfo(path, false)) == null) {
			cfi = getArgFileCacheFileInfo(path, false);
		}

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
			} else if (fSVDBFS.fileExists(target_dir + "/argfile")) {
				cfi = getArgFileCacheFileInfo(path, true);
				DataInput in = fSVDBFS.openDataInput(target_dir + "/argfile");
				file = readFile(in, path);
				fSVDBFS.closeInput(in);
				cfi.fSVDBFile = (Reference<SVDBFile>)createRef(file);
				cfi.fSVDBFileRef = file;
				fNumFilesRead++;
			}
		}
		
		return file;
	}
	
	public SVDBFile getArgFile(IProgressMonitor monitor, String path) {
		CacheFileInfo cfi = getArgFileCacheFileInfo(path, false);

		SVDBFile file = (cfi != null)?cfi.fSVDBFile.get():null;

		if (file == null) {
			String target_dir = computePathDir(path);
			
			if (fSVDBFS.fileExists(target_dir + "/argfile")) {
				cfi = getArgFileCacheFileInfo(path, true);
				DataInput in = fSVDBFS.openDataInput(target_dir + "/argfile");
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

	public void setFile(String path, SVDBFile file, boolean is_argfile) {
		CacheFileInfo cfi;
		String name;
		
		if (fDebugEn) {
			fLog.debug("setFile: path=" + path + " is_argfile=" + is_argfile);
		}
		
		if (is_argfile) {
			cfi = getArgFileCacheFileInfo(path, true);
			name = "argfile";
		} else {
			if (path.endsWith(".f")) {
				try {
					throw new Exception();
				} catch (Exception e ) {
					e.printStackTrace();
				}
			}
			cfi = getCacheFileInfo(path, true);
			name = "file";
		}
		
		if (file == null) {
			if (fDebugEn) {
				fLog.debug(LEVEL_MAX, "setFile \"" + path + "\" == NULL");
			}
			// TODO: should actually remove?
			cfi.fSVDBFile = new WeakReference<SVDBFile>(null);
			String target_dir = computePathDir(path);
			fSVDBFS.delete(new NullProgressMonitor(), target_dir + "/" + name);
		} else {
			cfi.fSVDBFile = (Reference<SVDBFile>)createRef(file);
			cfi.fSVDBFileRef = file;

			writeBackFile(path, file, is_argfile);
		}
	}
	
	public void setFileTree(String path, SVDBFileTree file_tree, boolean is_argfile) {
		CacheFileInfo cfi;
		
		if (is_argfile) {
			cfi = getArgFileCacheFileInfo(path, true);
		} else {
			cfi = getCacheFileInfo(path, true);
		}
		
		cfi.fSVDBFileTree = (Reference<SVDBFileTree>)createRef(file_tree);
		cfi.fSVDBFileTreeRef = file_tree;
		
		writeBackFileTree(path, file_tree);
	}
	
	public SVDBFileTree getFileTree(IProgressMonitor monitor, String path, boolean is_argfile) {
		CacheFileInfo cfi;
		
		monitor.beginTask("getFileTree", 1);
		if (is_argfile) {
			cfi = getArgFileCacheFileInfo(path, false);
		} else {
			cfi = getCacheFileInfo(path, false);
		}
		
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
		
		monitor.worked(1);
		monitor.done();
		return ft;
	}
	

	public void removeFile(String path, boolean is_argfile) {
		CacheFileInfo file;
		
		if (is_argfile) {
			file = fArgFileCache.get(path);
			fArgFileCache.remove(path);
		} else {
			file = fFileCache.get(path);
			fFileCache.remove(path);
		}
		
		// Remove from linked list
		removeElement(file);
		
		String target_dir = computePathDir(path);

		// remove backing cache, if it exists
		fSVDBFS.delete(null, target_dir);
	}
	
	private String computePathDir(String path) {
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
		
		try {
			DataOutput out = fSVDBFS.openDataOutput("index");
			if (out == null) {
				throw new DBWriteException("Failed to open file \"index\" for writing");
			}
			writer.init(out);
			writer.writeString(fBaseLocation);
			List<String> tmp = new ArrayList<String>();
			
			tmp.clear();
			tmp.addAll(fFileCache.keySet());
			writer.writeStringList(tmp);
	
			tmp.clear();
			tmp.addAll(fArgFileCache.keySet());
			writer.writeStringList(tmp);
			
			List<Long> timestamp_list = new ArrayList<Long>();
			for (String path : fFileCache.keySet()) {
				CacheFileInfo cfi = getCacheFileInfo(path, true);
				timestamp_list.add(cfi.fLastModified);
			}
			writer.writeLongList(timestamp_list);
			
			timestamp_list.clear();
			for (String path : fArgFileCache.keySet()) {
				CacheFileInfo cfi = getArgFileCacheFileInfo(path, true);
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
	
		writeBackFileWorker(target_dir, file_path, file);
	}

	private void writeBackFile(String path, SVDBFile file, boolean is_argfile) {
		String target_dir = computePathDir(path);
		String file_path = target_dir + 
				((is_argfile)?"/argfile":"/file");
		
		writeBackFileWorker(target_dir, file_path, file);
	}
	
	private void writeBackFileTree(String path, SVDBFileTree file_tree) {
		String target_dir = computePathDir(path);
		String file_path = target_dir + "/fileTreeMap";

		writeBackFileTreeWorker(target_dir, file_path, file_tree);
	}
	
	private void writeBackMarkerList(String path, List<SVDBMarker> markers) {
		String target_dir = computePathDir(path);
		String file_path  = target_dir + "/markers";

		writeBackMarkerListWorker(target_dir, file_path, markers);
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
		synchronized (SVDBFileIndexCacheOld.class) {
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
		synchronized (SVDBFileIndexCacheOld.class) {
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
		synchronized (SVDBFileIndexCacheOld.class) {
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

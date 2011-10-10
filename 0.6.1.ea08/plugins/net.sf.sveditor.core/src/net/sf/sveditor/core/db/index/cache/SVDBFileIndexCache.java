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
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBFileIndexCache implements ISVDBIndexCache {
	private String							fBaseLocation;
	private List<String>					fFileList;
	private Map<String, Long>				fLastModifiedMap;
	private Map<String, SVDBFile>			fPreProcFileMap;
	private Map<String, SVDBFileTree>		fFileTreeMap;
	private Map<String, SVDBFile>			fFileMap;
	private Map<String, List<SVDBMarker>>	fMarkerMap;
	private ISVDBFS							fSVDBFS;
	private Object							fIndexData;
	private LogHandle						fLog;
	private	SVDBPersistenceReader 			fPersistenceRdr;
	private SVDBPersistenceWriter			fPersistenceWriter;
	private static final int				fCacheSize = 100000;

	
	public SVDBFileIndexCache(ISVDBFS fs) {
		fSVDBFS = fs;
		fFileList = new ArrayList<String>();
		fLastModifiedMap = new HashMap<String, Long>(fCacheSize);
		fPreProcFileMap = new WeakHashMap<String, SVDBFile>(fCacheSize);
		fFileTreeMap = new WeakHashMap<String, SVDBFileTree>(fCacheSize);
		fFileMap = new WeakHashMap<String, SVDBFile>(fCacheSize);
		fMarkerMap = new WeakHashMap<String, List<SVDBMarker>>(fCacheSize);
		fLog = LogFactory.getLogHandle("SVDBFileIndexCache");
		fPersistenceRdr = new SVDBPersistenceReader();
		fPersistenceWriter = new SVDBPersistenceWriter();
	}

	public SVDBFileIndexCache(ISVDBFS fs, int cache_sz) {
		fSVDBFS = fs;
		fFileList = new ArrayList<String>();
		fLastModifiedMap = new HashMap<String, Long>();
		fPreProcFileMap = new WeakHashMap<String, SVDBFile>(cache_sz);
		fFileTreeMap = new WeakHashMap<String, SVDBFileTree>(cache_sz);
		fFileMap = new WeakHashMap<String, SVDBFile>(cache_sz);
		fMarkerMap = new WeakHashMap<String, List<SVDBMarker>>(cache_sz);
		fLog = LogFactory.getLogHandle("SVDBFileIndexCache");
		
		debug("Create Cache: " + fs.getRoot());
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
		fLog.debug("clear");
		fFileList.clear();
		fLastModifiedMap.clear();
		fPreProcFileMap.clear();
		fFileTreeMap.clear();
		fFileMap.clear();
		fMarkerMap.clear();
		fSVDBFS.delete("");
	}

	public void addFile(String path) {
		if (!fFileList.contains(path)) {
			fFileList.add(path);
		}
	}
	
	public void setMarkers(String path, List<SVDBMarker> markers) {
		if (fMarkerMap.containsKey(path)) {
			fMarkerMap.remove(path);
		}
		
		fMarkerMap.put(path, markers);
		
		String parent_dir = computePathDir(path);
		fSVDBFS.mkdirs(parent_dir);
		String target_file = parent_dir + "/markers";
		writeMarkerList(target_file, markers);
	}
	
	public List<SVDBMarker> getMarkers(String path) {
		List<SVDBMarker> m = null;
		if (fMarkerMap.containsKey(path)) {
			m = fMarkerMap.get(path);
		} else {
			String parent_dir = computePathDir(path);
			String target_file = parent_dir + "/markers";
			if (fSVDBFS.fileExists(target_file)){
				List<SVDBMarker> marker_list = readMarkerList(target_file);
				fMarkerMap.put(path, marker_list);
			}
		}
		
		return m;
	}


	public boolean init(IProgressMonitor monitor, Object index_data) {
		boolean valid = false;
		fFileList.clear();
		fBaseLocation = "";
		fIndexData = index_data;

		// Read the file list from the backing file
		try {
			RandomAccessFile in = null;
			
			in = fSVDBFS.openChannelRead("index");
			
			if (in != null) {
				fPersistenceRdr.init(in);
				fBaseLocation = fPersistenceRdr.readString();
				fFileList = fPersistenceRdr.readStringList();
				List<Long> timestamp_list = fPersistenceRdr.readLongList();
				for (int i=0; i<fFileList.size() && i<timestamp_list.size(); i++) {
					fLastModifiedMap.put(fFileList.get(i), timestamp_list.get(i));
				}
				
				fSVDBFS.closeChannel(in);
			}
			
			in = fSVDBFS.openChannelRead("index_data");
			if (in != null) {
				fPersistenceRdr.init(in);
				fPersistenceRdr.readObject(null, index_data.getClass(), index_data);
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

	public List<String> getFileList() {
		return fFileList;
	}
	
	public long getLastModified(String path) {
		if (fLastModifiedMap.containsKey(path)) {
			return fLastModifiedMap.get(path);
		}
		return -1;
	}
	
	public void setLastModified(String path, long timestamp) {
		if (fLastModifiedMap.containsKey(path)) {
			fLastModifiedMap.remove(path);
		}
		fLastModifiedMap.put(path, timestamp);
	}

	public SVDBFile getPreProcFile(IProgressMonitor monitor, String path) {
		if (fPreProcFileMap.containsKey(path)) {
			return fPreProcFileMap.get(path);
		}
		String target_dir = computePathDir(path);
		
		if (fSVDBFS.fileExists(target_dir + "/preProcFile")) {
			SVDBFile f = null;
			RandomAccessFile in = fSVDBFS.openChannelRead(target_dir + "/preProcFile"); 
			f = readFile(in, path);
			fSVDBFS.closeChannel(in);
			fPreProcFileMap.put(path, f);
			return f;
		}

		return null;
	}

	public SVDBFile getFile(IProgressMonitor monitor, String path) {
		if (fFileMap.containsKey(path)) {
			return fFileMap.get(path);
		}
		String target_dir = computePathDir(path);
		
		if (fSVDBFS.fileExists(target_dir + "/file")) {
			SVDBFile f = null;
			//				debug("readFile: " + path);
			RandomAccessFile in = fSVDBFS.openChannelRead(target_dir + "/file"); 
			f = readFile(in, path);
			fSVDBFS.closeChannel(in);
			fFileMap.put(path, f);
			return f;
		} else {
			debug("Target dir does not exist: " + target_dir);
		}

		return null;
	}

	public void setPreProcFile(String path, SVDBFile file) {
		if (file == null) {
			try {
				throw new Exception("SVDBFile for path \"" + path + "\" is null");
			} catch (Exception e) {
				fLog.error("SVDBFile for path \"" + path + "\" is null", e);
			}
		}

		if (fPreProcFileMap.containsKey(path)) {
			fPreProcFileMap.remove(path);
		}
		fPreProcFileMap.put(path, file);
		
		// write-through to the cache
		String target_dir = computePathDir(path);
		fSVDBFS.mkdirs(target_dir);
		try {
			RandomAccessFile out = fSVDBFS.openChannelWrite(target_dir + "/preProcFile");
			
			fPersistenceWriter.init(out);
			fPersistenceWriter.writeObject(file.getClass(), file);
			fPersistenceWriter.close();
			fSVDBFS.closeChannel(out);
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}

	public void setFile(String path, SVDBFile file) {
		if (file == null) {
			debug("setFile \"" + path + "\" == NULL");
			fFileMap.remove(path);
			String target_dir = computePathDir(path);
			fSVDBFS.delete(target_dir + "/file");
		} else {
			if (fFileMap.containsKey(path)) {
				fFileMap.remove(path);
			}
			fFileMap.put(path, file);

			String target_dir = computePathDir(path);
			fSVDBFS.mkdirs(target_dir);
			
			try {
				RandomAccessFile out = fSVDBFS.openChannelWrite(target_dir + "/file");
				fPersistenceWriter.init(out);
				fPersistenceWriter.writeObject(file.getClass(), file);
				fPersistenceWriter.close();
				out.close();
			} catch (IOException e) {
				e.printStackTrace();
			} catch (DBWriteException e) {
				e.printStackTrace();
			}
		}
	}

	public void setFileTree(String path, SVDBFileTree file_tree) {
		if (fFileTreeMap.containsKey(path)) {
			fFileTreeMap.remove(path);
		}
		fFileTreeMap.put(path, file_tree);
		
		String target_dir = computePathDir(path);
		fSVDBFS.mkdirs(target_dir);
		
		try {
			RandomAccessFile out = fSVDBFS.openChannelWrite(target_dir + "/fileTreeMap");
			fPersistenceWriter.init(out);
			fPersistenceWriter.writeObject(file_tree.getClass(), file_tree);
			fPersistenceWriter.close();
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}
	
	public SVDBFileTree getFileTree(IProgressMonitor monitor, String path) {
		if (fFileTreeMap.containsKey(path)) {
			return fFileTreeMap.get(path);
		}
		String target_dir = computePathDir(path);
		
		if (fSVDBFS.fileExists(target_dir + "/fileTreeMap")) {
			SVDBFileTree f = null;
			RandomAccessFile in = fSVDBFS.openChannelRead(target_dir + "/fileTreeMap"); 
			f = readFileTree(in);
			fSVDBFS.closeChannel(in);

			fFileTreeMap.put(path, f);
			return f;
		}

		return null;
	}
	

	public void removeFile(String path) {
		fFileList.remove(path);
		fFileMap.remove(path);
		fFileTreeMap.remove(path);
		fPreProcFileMap.remove(path);
		
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
//		debug("readFile " + path);
		fPersistenceRdr.init(in);
		
		SVDBFile ret = new SVDBFile();
		try {
			fPersistenceRdr.readObject(null, ret.getClass(), ret);
		} catch (DBFormatException e) {
			e.printStackTrace();
		}

		return ret;
	}

	private SVDBFileTree readFileTree(RandomAccessFile in) {
//		debug("readFileTree");
		fPersistenceRdr.init(in);
		
		SVDBFileTree ret = new SVDBFileTree();
		try {
			fPersistenceRdr.readObject(null, ret.getClass(), ret);
		} catch (DBFormatException e) {
			e.printStackTrace();
		}
		
		return ret;
	}
	
	@SuppressWarnings("unchecked")
	private List<SVDBMarker> readMarkerList(String path) {
//		InputStream in = null;
		RandomAccessFile in = fSVDBFS.openChannelRead(path);
		fPersistenceRdr.init(in);
		
		List<SVDBMarker> ret = null;
		
		try {
			ret = (List<SVDBMarker>)fPersistenceRdr.readItemList(null);
		} catch (DBFormatException e) {
			e.printStackTrace();
		}

		fSVDBFS.closeChannel(in);
		
		return ret;
	}
	
	private void writeMarkerList(String path, List<SVDBMarker> marker_list) {
		try {
			RandomAccessFile out = fSVDBFS.openChannelWrite(path);
			fPersistenceWriter.init(out);
			fPersistenceWriter.writeItemList(marker_list);
			fPersistenceWriter.close();
			fSVDBFS.closeChannel(out);
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}

	public void sync() {
		
		try {
			RandomAccessFile out = fSVDBFS.openChannelWrite("index");
			if (out == null) {
				throw new DBWriteException("Failed to open file \"index\" for writing");
			}
			fPersistenceWriter.init(out);
			fPersistenceWriter.writeString(fBaseLocation);
			fPersistenceWriter.writeStringList(fFileList);
			List<Long> timestamp_list = new ArrayList<Long>();
			for (String path : fFileList) {
				if (fLastModifiedMap.containsKey(path)) {
					timestamp_list.add(fLastModifiedMap.get(path));
				} else {
					timestamp_list.add(-1L);
					fLog.error("LastModifiedList does not contain \"" + path + "\"");
				}
			}
			fPersistenceWriter.writeLongList(timestamp_list);
			
			fPersistenceWriter.close();
			fSVDBFS.closeChannel(out);
			
			out = fSVDBFS.openChannelWrite("index_data");
			fPersistenceWriter.init(out);
			fPersistenceWriter.writeObject(fIndexData.getClass(), fIndexData);
			fPersistenceWriter.close();
			fSVDBFS.closeChannel(out);
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}
	
	private void debug(String msg) {
		// TODO:
	}
	
}

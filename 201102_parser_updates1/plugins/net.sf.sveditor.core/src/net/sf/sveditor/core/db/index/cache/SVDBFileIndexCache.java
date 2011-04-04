package net.sf.sveditor.core.db.index.cache;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
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
	
	public SVDBFileIndexCache(ISVDBFS fs) {
		fSVDBFS = fs;
		fFileList = new ArrayList<String>();
		fLastModifiedMap = new HashMap<String, Long>();
		fPreProcFileMap = new WeakHashMap<String, SVDBFile>();
		fFileTreeMap = new WeakHashMap<String, SVDBFileTree>();
		fFileMap = new WeakHashMap<String, SVDBFile>();
		fMarkerMap = new WeakHashMap<String, List<SVDBMarker>>();
		fLog = LogFactory.getLogHandle("SVDBFileIndexCache");
	}

	public SVDBFileIndexCache(ISVDBFS fs, int cache_sz) {
		fSVDBFS = fs;
		fFileList = new ArrayList<String>();
		fLastModifiedMap = new HashMap<String, Long>();
		fPreProcFileMap = new WeakHashMap<String, SVDBFile>(cache_sz);
		fFileTreeMap = new WeakHashMap<String, SVDBFileTree>(cache_sz);
		fFileMap = new WeakHashMap<String, SVDBFile>(cache_sz);
		fMarkerMap = new WeakHashMap<String, List<SVDBMarker>>();
		fLog = LogFactory.getLogHandle("SVDBFileIndexCache");
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
		fPreProcFileMap.clear();
		fFileTreeMap.clear();
		fFileMap.clear();
		fLastModifiedMap.clear();
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


	public void init(IProgressMonitor monitor, Object index_data) {
		fFileList.clear();
		fBaseLocation = "";
		
		// Read the file list from the backing file
		try {
			InputStream in;
			SVDBPersistenceReader rdr;
			
			in = fSVDBFS.openFileRead("index");
			if (in != null) {
				rdr = new SVDBPersistenceReader(in);
				fBaseLocation = rdr.readString();
				fFileList = rdr.readStringList();
				List<Long> timestamp_list = rdr.readLongList();
				for (int i=0; i<fFileList.size() && i<timestamp_list.size(); i++) {
					fLastModifiedMap.put(fFileList.get(i), timestamp_list.get(i));
				}
				in.close();
			}
			
			in = fSVDBFS.openFileRead("index_data");
			if (in != null) {
				rdr = new SVDBPersistenceReader(in);
				rdr.readObject(null, index_data.getClass(), index_data);
			}
			fIndexData = index_data;
		} catch (IOException e) {}
		  catch (DBFormatException e) {
			  e.printStackTrace();
		}
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
			try {
				f = readFile(fSVDBFS.openFileRead(target_dir + "/preProcFile"), path);
				fPreProcFileMap.put(path, f);
				return f;
			} catch (IOException e) {
				e.printStackTrace();
			}
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
			try {
				f = readFile(fSVDBFS.openFileRead(target_dir + "/file"), path);
				fFileMap.put(path, f);
				return f;
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		return null;
	}

	public void setPreProcFile(String path, SVDBFile file) {
		path = computePathDir(path);
		
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
			OutputStream out = fSVDBFS.openFileWrite(target_dir + "/preProcFile");
			SVDBPersistenceWriter writer = new SVDBPersistenceWriter(out);
			writer.writeObject(file.getClass(), file);
			writer.close();
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}

	public void setFile(String path, SVDBFile file) {
		if (fFileMap.containsKey(path)) {
			fFileMap.remove(path);
		}
		fFileMap.put(path, file);

		String target_dir = computePathDir(path);
		fSVDBFS.mkdirs(target_dir);
		
		try {
			OutputStream out = fSVDBFS.openFileWrite(target_dir + "/file");
			SVDBPersistenceWriter writer = new SVDBPersistenceWriter(out);
			writer.writeObject(file.getClass(), file);
			writer.close();
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (DBWriteException e) {
			e.printStackTrace();
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
			OutputStream out = fSVDBFS.openFileWrite(target_dir + "/fileTreeMap");
			SVDBPersistenceWriter writer = new SVDBPersistenceWriter(out);
			writer.writeObject(file_tree.getClass(), file_tree);
			writer.close();
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
			try {
				f = readFileTree(fSVDBFS.openFileRead(target_dir + "/fileTreeMap"));
				
				fFileTreeMap.put(path, f);
				return f;
			} catch (IOException e) {
				e.printStackTrace();
			}
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
		String ret = path;
		ret = ret.replace('/', '_');
		ret = ret.replace('$', '_');
		ret = ret.replace('{', '_');
		ret = ret.replace('}', '_');

		return ret;
	}
	
	private SVDBFile readFile(InputStream in, String path) {
//		System.out.println("readFile " + path);
		SVDBPersistenceReader rdr = new SVDBPersistenceReader(in);
		
		SVDBFile ret = new SVDBFile();
		try {
			rdr.readObject(null, ret.getClass(), ret);
		} catch (DBFormatException e) {
			e.printStackTrace();
		}

		try {
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return ret;
	}

	private SVDBFileTree readFileTree(InputStream in) {
//		System.out.println("readFileTree");
		SVDBPersistenceReader rdr = new SVDBPersistenceReader(in);
		
		SVDBFileTree ret = new SVDBFileTree();
		try {
			rdr.readObject(null, ret.getClass(), ret);
		} catch (DBFormatException e) {
			e.printStackTrace();
		}

		try {
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return ret;
	}
	
	@SuppressWarnings("unchecked")
	private List<SVDBMarker> readMarkerList(String path) {
		InputStream in = null;
		try {
			in = fSVDBFS.openFileRead(path);
		} catch (IOException e) { }
		
		SVDBPersistenceReader rdr = new SVDBPersistenceReader(in);
		
		List<SVDBMarker> ret = null;
		
		try {
			ret = (List<SVDBMarker>)rdr.readItemList(null);
		} catch (DBFormatException e) {
			e.printStackTrace();
		}

		fSVDBFS.close(in);
		
		return ret;
	}
	
	private void writeMarkerList(String path, List<SVDBMarker> marker_list) {
		try {
			OutputStream out = fSVDBFS.openFileWrite(path);
			SVDBPersistenceWriter writer = new SVDBPersistenceWriter(out);
			writer.writeItemList(marker_list);
			writer.close();
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}

	public void sync() {
		SVDBPersistenceWriter wrt = null;
		
		try {
			OutputStream out;
			
			out = fSVDBFS.openFileWrite("index");
			if (out == null) {
				throw new DBWriteException("Failed to open file \"index\" for writing");
			}
			wrt = new SVDBPersistenceWriter(out);
			wrt.writeString(fBaseLocation);
			wrt.writeStringList(fFileList);
			List<Long> timestamp_list = new ArrayList<Long>();
			for (String path : fFileList) {
				timestamp_list.add(fLastModifiedMap.get(path));
			}
			wrt.writeLongList(timestamp_list);
			
			wrt.close();
			out.close();
			
			out = fSVDBFS.openFileWrite("index_data");
			wrt = new SVDBPersistenceWriter(out);
			wrt.writeObject(fIndexData.getClass(), fIndexData);
			wrt.close();
			out.close();
		} catch (IOException e) {
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}
	
}

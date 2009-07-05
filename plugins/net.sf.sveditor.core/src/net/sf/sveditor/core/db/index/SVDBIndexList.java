package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;

public class SVDBIndexList implements ISVDBIndexList, ISVDBIndexChangeListener {
	
	private List<ISVDBIndex>							fIndexList;
	private File										fProjectDir;
	private Map<String, SVDBFile>						fFileDB;
	private Map<String, SVDBFile>						fPreProcFileMap;
	private List<ISVDBIndexChangeListener>				fIndexChangeListeners;
	private ISVDBIndex									fSuperIndex;
	
	public SVDBIndexList(File project_dir) {
		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		fIndexList = new ArrayList<ISVDBIndex>();
		fProjectDir = project_dir;
		fSuperIndex = null;
	}
	
	public void init(ISVDBIndexRegistry registry) {
		// nothing
	}

	public void dispose() {
		for (ISVDBIndex idx : fIndexList) {
			idx.removeChangeListener(this);
		}
	}
	
	public String getTypeID() {
		return "net.sf.sveditor.svdb_index_list";
	}

	@Override
	public ISVDBItemIterator<SVDBItem> getItemIterator() {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean isLoaded() {
		// Doesn't really matter
		return false;
	}
	
	public void load(List<SVDBFile> pp_list, List<SVDBFile> db_list) {
		System.out.println("[ERROR] cannot load an index list");
	}

	public String getBaseLocation() {
		return fProjectDir.getAbsolutePath(); 
	}
	
	public void setSuperIndex(ISVDBIndex index) {
		fSuperIndex = index;
	}
	
	public ISVDBIndex getSuperIndex() {
		return fSuperIndex;
	}
	
	/*
	public SVDBFile findIncludedFile(String leaf) {
		SVDBFile ret = null;
		
		for (ISVDBIndex index : fIndexList) {
			if ((ret = index.findIncludedFile(leaf)) != null) {
				break;
			}
		}
		
		return ret;
	}
	 */

	public synchronized Map<String, SVDBFile> getFileDB() {
		if (fFileDB == null) {
			fFileDB = new HashMap<String, SVDBFile>();
			for (ISVDBIndex index : fIndexList) {
				fFileDB.putAll(index.getFileDB());
			}
		}
		
		return fFileDB;
	}

	public synchronized Map<String, SVDBFile> getPreProcFileMap() {
		
		if (fPreProcFileMap == null) {
			fPreProcFileMap = new HashMap<String, SVDBFile>();
			
			for (ISVDBIndex index : fIndexList) {
				fPreProcFileMap.putAll(index.getPreProcFileMap());
			}
		}
		
		return fPreProcFileMap;
	}
	
	public SVDBFile findFile(String file) {
		synchronized (fIndexList) {
			for (ISVDBIndex index : fIndexList) {
				SVDBFile ret;
				
				if ((ret = index.findFile(file)) != null) {
					return ret;
				}
			}
		}
		
		return null;
	}

	public SVDBFile findPreProcFile(String path) {
		synchronized (fIndexList) {
			for (ISVDBIndex index : fIndexList) {
				SVDBFile ret;
				
				if ((ret = index.findFile(path)) != null) {
					return ret;
				}
			}
		}

		System.out.println("[WARN] failed to file pre-proc file \"" + 
				path + "\" in index list");
		return null;
	}

	public int getIndexType() {
		return IT_IndexList;
	}

	public void rebuildIndex() {
		for (ISVDBIndex idx : fIndexList) {
			idx.rebuildIndex();
		}
	}

	public void addIndex(ISVDBIndex idx) {
		if (!fIndexList.contains(idx)) {
			// TODO: signal change event?
			fIndexList.add(idx);
			idx.addChangeListener(this);
		}
	}
	
	public void removeIndex(ISVDBIndex idx) {
		// TODO: signal change event?
		fIndexList.remove(idx);
		idx.removeChangeListener(this);
	}
	
	public SVDBFile parse(InputStream in, String path) {
		System.out.println("SVDBIndexList.parse()");
		// TODO Auto-generated method stub
		return null;
	}

	public List<ISVDBIndex> getIndexList() {
		return fIndexList;
	}
	
	public void addChangeListener(ISVDBIndexChangeListener l) {
		fIndexChangeListeners.add(l);
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		fIndexChangeListeners.remove(l);
	}

	public void index_changed(int reason, SVDBFile file) {
		if (reason == ISVDBIndexChangeListener.FILE_ADDED) {
			if (fFileDB != null) {
				fFileDB.put(file.getFilePath(), file);
			}
			if (fPreProcFileMap != null) {
				fPreProcFileMap.put(file.getFilePath(), file);
			}
		} else if (reason == ISVDBIndexChangeListener.FILE_REMOVED) {
			if (fFileDB != null) {
				fFileDB.remove(file.getFilePath());
			}
			if (fPreProcFileMap != null) {
				fPreProcFileMap.remove(file.getFilePath());
			}
		} else if (reason == ISVDBIndexChangeListener.FILE_CHANGED) {
			
		}
		
		for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
			l.index_changed(reason, file);
		}
	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider inc_provider) {
		// TODO Auto-generated method stub
		
	}
	
	
}


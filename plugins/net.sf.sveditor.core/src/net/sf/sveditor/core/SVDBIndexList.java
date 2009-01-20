package net.sf.sveditor.core;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;

public class SVDBIndexList implements ISVDBIndexList {
	
	private List<ISVDBIndex>				fIndexList;
	private File							fProjectDir;
	private Map<File, SVDBFile>				fFileDB;
	private Map<File, SVDBFileTree>			fFileTree;
	
	public SVDBIndexList(File project_dir) {
		fIndexList = new ArrayList<ISVDBIndex>();
		fProjectDir = project_dir;
	}

	public void dispose() {
		for (ISVDBIndex idx : fIndexList) {
			idx.dispose();
		}
	}

	public File getBaseLocation() {
		return fProjectDir; 
	}
	
	@Override
	public SVDBFileTree findIncludedFile(String leaf) {
		System.out.println("[TODO] findIncludedFile(" + leaf + ")");
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Map<File, SVDBFile> getFileDB() {
		if (fFileDB == null) {
			fFileDB = new HashMap<File, SVDBFile>();
			for (ISVDBIndex index : fIndexList) {
				fFileDB.putAll(index.getFileDB());
			}
		}
		
		return fFileDB;
	}

	@Override
	public Map<File, SVDBFileTree> getFileTree() {
		if (fFileTree == null) {
			fFileTree = new HashMap<File, SVDBFileTree>();
			
			for (ISVDBIndex index : fIndexList) {
				fFileTree.putAll(index.getFileTree());
			}
		}

		return fFileTree;
	}

	@Override
	public int getIndexType() {
		return IT_IndexList;
	}

	@Override
	public void rebuildIndex() {
		for (ISVDBIndex idx : fIndexList) {
			idx.rebuildIndex();
		}
	}

	public void addIndex(ISVDBIndex idx) {
		// TODO: signal change event?
		fIndexList.add(idx);
	}
	
	public void removeIndex(ISVDBIndex idx) {
		// TODO: signal change event?
		fIndexList.remove(idx);
	}
	
	public List<ISVDBIndex> getIndexList() {
		return fIndexList;
	}
	
	/*
	public List<SVDBFile> getFileList() {
		List<SVDBFile> ret = new ArrayList<SVDBFile>();
		
		for (ISVDBIndex idx : fIndexList) {
			ret.addAll(idx.getFileList());
		}
		
		return ret;
	}
	 */
}

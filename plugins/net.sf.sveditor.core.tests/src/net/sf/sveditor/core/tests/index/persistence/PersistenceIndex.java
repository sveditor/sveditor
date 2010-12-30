/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.persistence;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIncludeFileProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexRegistry;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

public class PersistenceIndex implements ISVDBIndex {
	private ISVDBIndex 				fTargetIndex;
	private List<SVDBFile>			fDumpDBFileList;
	private List<SVDBFile>			fDumpPPFileList;
	private List<SVDBFile>			fLoadDBFileList;
	private List<SVDBFile>			fLoadPPFileList;
	
	public PersistenceIndex(ISVDBIndex index) {
		fTargetIndex = index;
		fDumpDBFileList = new ArrayList<SVDBFile>();
		fDumpPPFileList = new ArrayList<SVDBFile>();
		fLoadDBFileList = new ArrayList<SVDBFile>();
		fLoadPPFileList = new ArrayList<SVDBFile>();
	}
	
	public List<SVDBFile> getDumpDBFileList() {
		return fDumpDBFileList;
	}
	
	public List<SVDBFile> getDumpPPFileList() {
		return fDumpPPFileList;
	}
	
	public List<SVDBFile> getLoadDBFileList() {
		return fLoadDBFileList;
	}
	
	public List<SVDBFile> getLoadPPFileList() {
		return fLoadPPFileList;
	}

	public void dump(IDBWriter indexData) {
		fDumpPPFileList.addAll(getPreProcFileMap().values());
		fDumpDBFileList.addAll(getFileDB().values());
		fTargetIndex.dump(indexData);
	}

	public void load(IDBReader indexData, List<SVDBFile> ppFiles,
			List<SVDBFile> dbFiles) throws DBFormatException {
		fLoadPPFileList.addAll(ppFiles);
		fLoadDBFileList.addAll(dbFiles);

		fTargetIndex.load(indexData, ppFiles, dbFiles);
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {}
	public void clearGlobalDefines() {}
	public void dispose() {}
	public SVDBFile findFile(String path) {
		return null;
	}

	public SVDBFile findPreProcFile(String path) {
		return null;
	}

	public String getBaseLocation() {
		return fTargetIndex.getBaseLocation();
	}

	public Map<String, SVDBFile> getFileDB() {
		return fTargetIndex.getFileDB();
	}

	public Map<String, SVDBFile> getPreProcFileMap() {
		return fTargetIndex.getPreProcFileMap();
	}

	public String getTypeID() {
		return null;
	}

	public String getTypeName() {
		return null;
	}

	public void init(ISVDBIndexRegistry registry) {}

	public boolean isLoaded() {
		return false;
	}


	public SVDBFile parse(InputStream in, String path) {
		// TODO Auto-generated method stub
		return null;
	}

	public void rebuildIndex() {
		// TODO Auto-generated method stub

	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		// TODO Auto-generated method stub

	}

	public void setGlobalDefine(String key, String val) {
		// TODO Auto-generated method stub

	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider incProvider) {
		// TODO Auto-generated method stub

	}

	public ISVDBItemIterator getItemIterator() {
		return fTargetIndex.getItemIterator();
	}

	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		// TODO Auto-generated method stub
		return null;
	}

}

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


package net.sf.sveditor.core.tests.content_assist;

import java.io.InputStream;
import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.db.index.old.AbstractSVDBIndex;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

import org.eclipse.core.runtime.IProgressMonitor;

public class ContentAssistIndex extends AbstractSVDBIndex {
	private SVDBFile				fFile;
	
	public ContentAssistIndex() {
		super("GLOBAL", "base_location", 
				null, new InMemoryIndexCache(), null);
	}
	
	public void init(IProgressMonitor monitor) {
		init(monitor, null);
	}



	@Override
	protected String getLogName() {
		return "ContentAssistIndex";
	}

	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) { }

	public void setFile(SVDBFile file) {
		fFile = file;
		cacheDeclarations(fFile);
	}
	
	@Override
	public Set<String> getFileList(IProgressMonitor monitor) {
		Set<String> ret = new HashSet<String>();
		synchronized (fFile) {
			ret.add(fFile.getFilePath());
		}
		return ret;
	}

	@Override
	public synchronized SVDBFile findFile(String path) {
		return fFile;
	}

	@Override
	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		return super.getItemIterator(monitor);
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {}
	public String getBaseLocation() { return ""; }
	public String getTypeID() { return "ContentAssistIndex"; }
	public void removeChangeListener(ISVDBIndexChangeListener l) {}
	public SVDBFile parse(InputStream in, String path, IProgressMonitor monitor) { return null; }
	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) { return null; }

}

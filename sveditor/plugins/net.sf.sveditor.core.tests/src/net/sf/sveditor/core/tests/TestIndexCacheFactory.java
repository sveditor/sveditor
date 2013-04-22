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


package net.sf.sveditor.core.tests;

import java.io.File;
import java.io.IOException;
import java.util.List;

import junit.framework.TestCase;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.db.index.cache.SVDBDirFS;
import net.sf.sveditor.core.db.index.cache.SVDBFileIndexCacheOld;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;

public class TestIndexCacheFactory implements ISVDBIndexCacheMgr {
	private ISVDBIndexCacheMgr		fCacheImpl;
	private SVDBFileSystem			fFileSystem;
	private File					fRoot;
	
	public TestIndexCacheFactory(File dir) {
		fRoot = dir;
		
		if (fRoot == null) {
			fCacheImpl = InMemCacheMgr; 
		} else if (SVCorePlugin.fUseNewCacheMgr) {
			fCacheImpl = new SVDBFileIndexCacheMgr();
			fFileSystem = new SVDBFileSystem(fRoot, SVCorePlugin.getVersion());
			try {
				fFileSystem.init();
			} catch (IOException e) {
				TestCase.fail("Failed to initialize filesystem");
			}
			((SVDBFileIndexCacheMgr)fCacheImpl).init(fFileSystem);
		} else {
			fCacheImpl = OldCacheMgr;
		}
	}

	public ISVDBIndexCache createIndexCache(String project_name, String base_location) {
		return fCacheImpl.createIndexCache(project_name, base_location);
	}
	
	public ISVDBIndexCache findIndexCache(String project_name, String base_location) {
		return fCacheImpl.findIndexCache(project_name, base_location);
	}

	public void compactCache(List<ISVDBIndexCache> cache_list) {
		fCacheImpl.compactCache(cache_list);
	}

	public void dispose() {
		fCacheImpl.dispose();
	}

	public void sync() {
		fCacheImpl.sync();
	}

	public static TestIndexCacheFactory instance() {
		return new TestIndexCacheFactory(null);
	}
	
	private ISVDBIndexCacheMgr		InMemCacheMgr = new ISVDBIndexCacheMgr() {
		public ISVDBIndexCache createIndexCache(String project_name, String base_location) {
			return new InMemoryIndexCache();
		}
		
		public void sync() { }
		
		public void dispose() { }
		
		public void compactCache(List<ISVDBIndexCache> cache_list) { }
		
		public ISVDBIndexCache findIndexCache(String project_name, String base_location) {
			return null;
		}
	};
	
	private ISVDBIndexCacheMgr		OldCacheMgr = new ISVDBIndexCacheMgr() {
		
		public void sync() { }
		
		public void dispose() { }
		
		public ISVDBIndexCache findIndexCache(String project_name, String base_location) {
			return null;
		}
		
		public ISVDBIndexCache createIndexCache(String project_name, String base_location) {
			SVDBDirFS fs = new SVDBDirFS(fRoot);
			return new SVDBFileIndexCacheOld(fs);
		}
		
		public void compactCache(List<ISVDBIndexCache> cache_list) {
			// TODO Auto-generated method stub
			
		}
	};
}

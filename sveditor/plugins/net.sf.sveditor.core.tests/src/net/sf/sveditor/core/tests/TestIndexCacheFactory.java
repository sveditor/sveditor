/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests;

import java.io.File;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.index.cache.InMemoryIndexCache;

import junit.framework.TestCase;

public class TestIndexCacheFactory implements ISVDBIndexCacheMgr {
	private ISVDBIndexCacheMgr		fCacheImpl;
	private File					fRoot;
	
	public TestIndexCacheFactory(File dir) {
		fRoot = dir;
		
		if (fRoot == null) {
			fCacheImpl = InMemCacheMgr; 
		} else {
			fCacheImpl = SVCorePlugin.createCacheMgr(fRoot);
			TestCase.assertNotNull(fCacheImpl);
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
	
}

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
import java.util.List;

import junit.framework.TestCase;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;
import net.sf.sveditor.core.db.index.cache.SVDBDirFS;
import net.sf.sveditor.core.db.index.cache.SVDBFileIndexCache;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.db.index.cache.SVDBThreadedFileIndexCache;

public class TestIndexCacheFactory implements ISVDBIndexCacheFactory {
	private File				fRoot;
	
	public TestIndexCacheFactory(File dir) {
		fRoot = dir;
	}

	public ISVDBIndexCache createIndexCache(
			String project_name,
			String base_location) {
		if (fRoot == null) {
			return new InMemoryIndexCache();
		} else {
			if (!fRoot.isDirectory()) {
				TestCase.assertTrue(fRoot.mkdirs());
			}
			String hash = SVFileUtils.computeMD5(base_location);
			File target = new File(fRoot, project_name + "_" + hash);
//			System.out.println("Create index: " + target.getAbsolutePath());
			if (!target.isDirectory()) {
				TestCase.assertTrue(target.mkdirs());
			}
			
			SVDBFileIndexCache cache = new SVDBFileIndexCache(new SVDBDirFS(target));
//			SVDBThreadedFileIndexCache cache = new SVDBThreadedFileIndexCache(new SVDBDirFS(target));
			
			return cache;
		}
	}
	
	public void compactCache(List<ISVDBIndexCache> cache_list) { }

	public static TestIndexCacheFactory instance(File dir) {
		return new TestIndexCacheFactory(dir);
	}
}

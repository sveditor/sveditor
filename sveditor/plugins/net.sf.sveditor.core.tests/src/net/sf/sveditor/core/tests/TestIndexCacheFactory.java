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

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;

public class TestIndexCacheFactory extends SVDBFileIndexCacheMgr {
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
			return super.createIndexCache(project_name, base_location);
		}
	}
	
	public static TestIndexCacheFactory instance() {
		return new TestIndexCacheFactory(null);
	}
}

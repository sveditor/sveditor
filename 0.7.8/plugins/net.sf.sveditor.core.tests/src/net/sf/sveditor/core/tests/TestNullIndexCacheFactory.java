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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;

public class TestNullIndexCacheFactory implements ISVDBIndexCacheFactory {
	private List<TestNullIndexCache>			fCacheList;
	
	public TestNullIndexCacheFactory() {
		fCacheList = new ArrayList<TestNullIndexCache>();
	}

	public ISVDBIndexCache createIndexCache(String project_name,
			String base_location) {
		TestNullIndexCache ret = new TestNullIndexCache();
		fCacheList.add(ret);
		
		return ret;
	}

	public void compactCache(List<ISVDBIndexCache> cache_list) {
	}
	
	public List<TestNullIndexCache> getCacheList() {
		return fCacheList;
	}

}

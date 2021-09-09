/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.db.index.cache;

import java.util.List;

public class InMemoryIndexCacheMgr implements ISVDBIndexCacheMgr {

	@Override
	public ISVDBIndexCache findIndexCache(String project_name, String base_location) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVDBIndexCache createIndexCache(String project_name, String base_location) {
		return new InMemoryIndexCache(this);
	}

	@Override
	public void compactCache(List<ISVDBIndexCache> cache_list) { }

	@Override
	public void dispose() { }

	@Override
	public void sync() { }

}

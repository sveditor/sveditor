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
package org.sveditor.core.db.refs;

import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBRefCacheItem {
	
	private SVDBRefCacheEntry	fCacheEntry;
	private ISVDBRefFinder		fRefFinder;
	private SVDBRefType			fRefType;
	private String				fRefName;
	
	public SVDBRefCacheItem(
			SVDBRefCacheEntry			entry,
			ISVDBRefFinder				finder,
			SVDBRefType					type,
			String						name) {
		fCacheEntry = entry;
		fRefFinder = finder;
		fRefType = type;
		fRefName = name;
	}
	
	public void setRefFinder(ISVDBRefFinder finder) {
		fRefFinder = finder;
	}
	
	public String getFilename() {
		return fCacheEntry.getFilename();
	}
	
	public SVDBRefType getRefType() {
		return fRefType;
	}
	
	public String getRefName() {
		return fRefName;
	}

	/**
	 * 
	 * @return
	 */
	public List<SVDBRefItem> findReferences(IProgressMonitor monitor) {
//		return fRefFinder.findReferences(monitor, this);
		return null;
	}
}

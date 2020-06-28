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
package org.eclipse.hdt.sveditor.core.db.index;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

/**
 * Simple container that implements the DeclCacheItem. Allows us to
 * temporarily 'fake' using the decl cache
 * 
 * @author ballance
 *
 */
public class SVDBContainerDeclCacheItem extends SVDBDeclCacheItem {
	private ISVDBItemBase			fItem;
	
	public SVDBContainerDeclCacheItem(ISVDBItemBase item) {
		fItem = item;
	}

	@Override
	public String getName() {
		return SVDBItem.getName(fItem);
	}

	@Override
	public SVDBItemType getType() {
		return fItem.getType();
	}

	@Override
	public ISVDBItemBase getSVDBItem() {
		return fItem;
	}

}

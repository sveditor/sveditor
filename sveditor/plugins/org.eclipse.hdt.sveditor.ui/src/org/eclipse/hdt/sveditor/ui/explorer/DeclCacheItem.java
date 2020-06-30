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
package net.sf.sveditor.ui.explorer;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;

public class DeclCacheItem implements IProjectPathsData, IAdaptable {
	private IProjectPathsData		fParent;
	protected SVDBDeclCacheItem		fItem;
	
	public DeclCacheItem(
			IProjectPathsData 		p,
			SVDBDeclCacheItem		item) {
		fParent = p;
		fItem = item;
	}

	@Override
	public String getName() {
		return fItem.getName();
	}
	
	public void reset() { }
	
	
	public SVDBDeclCacheItem getItem() {
		return fItem;
	}

	@Override
	public Object getParent(Object element) {
		return fParent;
	}

	@Override
	public Object[] getChildren(Object parent) {
		return ProjectPathsContentProvider.NO_ELEMENTS;
	}
	
	@Override
	public boolean hasChildren() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	@SuppressWarnings({"rawtypes","unchecked"})
	public Object getAdapter(Class adapter) {
		if (adapter == SVDBDeclCacheItem.class) {
			return fItem;
		}
		return null;
	}
	
	

}

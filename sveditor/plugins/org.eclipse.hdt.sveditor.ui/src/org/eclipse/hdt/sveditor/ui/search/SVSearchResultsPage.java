/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.ui.search;

import org.eclipse.hdt.sveditor.ui.SVEditorUtil;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.search.ui.text.AbstractTextSearchViewPage;
import org.eclipse.search.ui.text.Match;
import org.eclipse.ui.PartInitException;

public class SVSearchResultsPage extends AbstractTextSearchViewPage implements IAdaptable {
	private SVSearchTreeContentProvider				fTreeContentProvider;
	private SVSearchTableContentProvider			fTableContentProvider;
	
	@Override
	protected void elementsChanged(Object[] objects) {
		if (fTreeContentProvider != null) {
			fTreeContentProvider.elementsChanged(objects);
		}
		if (fTableContentProvider != null) {
			fTableContentProvider.elementsChanged(objects);
		}
	}

	@Override
	protected void clear() {
		if (fTreeContentProvider != null) {
			fTreeContentProvider.clear();
		}
		if (fTableContentProvider != null) {
			fTableContentProvider.clear();
		}
	}

	@Override
	protected void configureTreeViewer(TreeViewer viewer) {
		fTreeContentProvider = new SVSearchTreeContentProvider(this, viewer);
		viewer.setLabelProvider(new SVSearchTreeLabelProvider());
		viewer.setContentProvider(fTreeContentProvider);
	}

	@Override
	protected void configureTableViewer(TableViewer viewer) {
		fTableContentProvider = new SVSearchTableContentProvider(this, viewer);
		SVSearchTableLabelProvider provider = new SVSearchTableLabelProvider(); 
		viewer.setContentProvider(fTableContentProvider);
		viewer.setLabelProvider(new SVDecoratingSearchTableLabelProvider(provider));
	}
	
	@Override
	protected void showMatch(
			Match match, 
			int currentOffset, 
			int currentLength,
			boolean activate) throws PartInitException {
		ISVDBItemBase item = null;
		
		if (match.getElement() instanceof ISVDBItemBase) {
			item = (ISVDBItemBase)match.getElement();
		} else if (match.getElement() instanceof SVDBDeclCacheItem) {
			item = ((SVDBDeclCacheItem)match.getElement()).getSVDBItem();
		}
		
		if (item != null) {
			SVEditorUtil.openEditor(item);
		}
	}
	
	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		// TODO Auto-generated method stub
		return null;
	}

}

/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.search;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.ui.SVEditorUtil;

import org.eclipse.core.runtime.IAdaptable;
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
		if (match.getElement() instanceof ISVDBItemBase) {
			SVEditorUtil.openEditor((ISVDBItemBase)match.getElement());
		}
	}
	
	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		// TODO Auto-generated method stub
		return null;
	}

}

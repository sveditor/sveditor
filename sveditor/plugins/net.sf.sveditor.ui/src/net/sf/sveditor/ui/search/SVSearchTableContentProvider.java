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

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;

public class SVSearchTableContentProvider implements IStructuredContentProvider {
	private SVSearchResult			fResult;
	private TableViewer				fTableViewer;
	
	public SVSearchTableContentProvider(SVSearchResultsPage page, TableViewer viewer) {
		fTableViewer = viewer;
	}

	public void dispose() {
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fResult = (SVSearchResult)newInput;
	}

	public Object[] getElements(Object inputElement) {
		return fResult.getElements();
	}
	
	public synchronized void elementsChanged(Object[] updatedElements) {
		if (!fTableViewer.getControl().isDisposed()) {
			fTableViewer.refresh();
		}
	}

	public void clear() {
//		initialize(fResult);
		fTableViewer.refresh();
	}

}

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


package org.sveditor.ui.search;

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

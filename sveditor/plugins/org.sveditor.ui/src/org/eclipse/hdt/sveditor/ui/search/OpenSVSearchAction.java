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

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

public class OpenSVSearchAction implements IWorkbenchWindowActionDelegate {
	private static final String		SV_SEARCH_PAGE_ID = "org.eclipse.hdt.sveditor.ui.searchPage";
	
	private IWorkbenchWindow			fWindow;

	public void run(IAction action) {
        if (fWindow == null || fWindow.getActivePage() == null) {
            return;
        }
        NewSearchUI.openSearchDialog(fWindow, SV_SEARCH_PAGE_ID);
	}

	public void selectionChanged(IAction action, ISelection selection) {
		// TODO Auto-generated method stub

	}

	public void dispose() {
		fWindow = null;
	}

	public void init(IWorkbenchWindow window) {
		fWindow = window;
	}

}

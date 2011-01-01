package net.sf.sveditor.ui.search;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

public class OpenSVSearchAction implements IWorkbenchWindowActionDelegate {
	private static final String		SV_SEARCH_PAGE_ID = "net.sf.sveditor.ui.searchPage";
	
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

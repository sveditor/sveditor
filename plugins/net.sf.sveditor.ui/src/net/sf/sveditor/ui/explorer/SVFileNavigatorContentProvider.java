package net.sf.sveditor.ui.explorer;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBChangeListener;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

public class SVFileNavigatorContentProvider 
	implements ITreeContentProvider, Runnable,ISVDBChangeListener {
	
	private Viewer									fViewer;
	
	public SVFileNavigatorContentProvider() {
	}
	
	
	public void SVDBFileChanged(
			SVDBFile 			file, 
			List<SVDBItem> 		adds,
			List<SVDBItem> 		removes, 
			List<SVDBItem> 		changes) {
		Display.getDefault().asyncExec(this);
	}

	
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IFile) {
			IFile file = (IFile)parentElement;
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBProjectData pdata = pmgr.getProjectData(file.getProject());
			SVDBIndexCollectionMgr index_mgr = pdata.getProjectIndexMgr();
			
			List<SVDBSearchResult<SVDBFile>> res = 
				index_mgr.findFile("${workspace_loc}" + file.getFullPath());
			
			if (res.size() == 0) {
				System.out.println("SVFileNavigatorContentProvider: " +
						"failed to find \"" + file.getFullPath() + "\"");
			} else {
				return res.get(0).getItem().getItems().toArray();
			}
		} else if (parentElement instanceof SVDBScopeItem &&
				!(parentElement instanceof SVDBTaskFuncScope)) {
			return ((SVDBScopeItem)parentElement).getItems().toArray();
		}
		
		return new Object[0];
	}

	
	public Object getParent(Object element) {
		if (element instanceof IResource) {
			return ((IResource)element).getParent();
		} else if (element instanceof SVDBItem) {
			return ((SVDBItem)element).getParent();
		} else {
			return null;
		}
	}

	
	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

	
	public Object[] getElements(Object inputElement) {
		return new Object[0];
	}

	
	public void dispose() {
	}

	
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fViewer = viewer;
	}
	
	public void run() {
		if (!fViewer.getControl().isDisposed()) {
			fViewer.refresh();
		}
	}
}

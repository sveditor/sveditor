package net.sf.sveditor.ui.explorer;

import java.util.List;

import net.sf.sveditor.core.ISVDBChangeListener;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBWorkspaceFileManager;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

public class SVFileNavigatorContentProvider 
	implements ITreeContentProvider, Runnable,ISVDBChangeListener {
	
	private Viewer									fViewer;
	SVDBWorkspaceFileManager									fFileManager;
	
	public SVFileNavigatorContentProvider() {
		fFileManager = SVCorePlugin.getDefault().getSVDBMgr();
		fFileManager.addSVDBChangeListener(this);
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
			// File f = ((IFile)parentElement).getLocation().toFile();
			SVDBFile file = fFileManager.getFile((IFile)parentElement);
			
			if (file != null) {
				return file.getItems().toArray();
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
		fFileManager.removeSVDBChangeListener(this);
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

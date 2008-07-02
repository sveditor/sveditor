package net.sf.sveditor.ui.explorer;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.ISVDBChangeListener;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBFileManager;
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
	SVDBFileManager									fFileManager;
	
	public SVFileNavigatorContentProvider() {
		fFileManager = SVCorePlugin.getDefault().getSVDBMgr();
		fFileManager.addSVDBChangeListener(this);
	}
	
	@Override
	public void SVDBFileChanged(
			SVDBFile 			file, 
			List<SVDBItem> 		adds,
			List<SVDBItem> 		removes, 
			List<SVDBItem> 		changes) {
		Display.getDefault().asyncExec(this);
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IFile) {
			File f = ((IFile)parentElement).getLocation().toFile();
			SVDBFile file = fFileManager.getFile(f);
			
			if (file != null) {
				return file.getItems().toArray();
			}
		} else if (parentElement instanceof SVDBScopeItem &&
				!(parentElement instanceof SVDBTaskFuncScope)) {
			return ((SVDBScopeItem)parentElement).getItems().toArray();
		}
		
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof IResource) {
			return ((IResource)element).getParent();
		} else if (element instanceof SVDBItem) {
			return ((SVDBItem)element).getParent();
		} else {
			return null;
		}
	}

	@Override
	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

	@Override
	public Object[] getElements(Object inputElement) {
		return new Object[0];
	}

	@Override
	public void dispose() {
		fFileManager.removeSVDBChangeListener(this);
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fViewer = viewer;
	}
	
	public void run() {
		fViewer.refresh();
	}
}

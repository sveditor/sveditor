package net.sf.sveditor.ui.svcp;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVTreeContentProvider implements ITreeContentProvider {
	
	public Object[] getChildren(Object elem) {
		if (elem instanceof SVDBScopeItem &&
				!(elem instanceof SVDBTaskFuncScope)) {
			return ((SVDBScopeItem)elem).getItems().toArray();
		} else {
			return new Object[0];
		}
	}

	
	public Object getParent(Object element) {
		if (element instanceof SVDBItem) {
			return ((SVDBItem)element).getParent();
		} else {
			return null;
		}
	}

	
	public boolean hasChildren(Object element) {
		return ((element instanceof SVDBScopeItem) && 
				((SVDBScopeItem)element).getItems().size() > 0);
	}

	
	public Object[] getElements(Object element) {
		if (element instanceof SVDBScopeItem) {
			return ((SVDBScopeItem)element).getItems().toArray();
		} else {
			return new Object[0];
		}
	}

	
	public void dispose() {
		// TODO Auto-generated method stub

	}

	
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}
}

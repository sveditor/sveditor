package net.sf.sveditor.ui.svcp;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVTreeContentProvider implements ITreeContentProvider {
	
	private SVDBScopeItem				fRoot;
	
	@Override
	public Object[] getChildren(Object elem) {
		if (elem instanceof SVDBScopeItem &&
				!(elem instanceof SVDBTaskFuncScope)) {
			return ((SVDBScopeItem)elem).getItems().toArray();
		} else {
			return new Object[0];
		}
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof SVDBItem) {
			return ((SVDBItem)element).getParent();
		} else {
			return null;
		}
	}

	@Override
	public boolean hasChildren(Object element) {
		return ((element instanceof SVDBScopeItem) && 
				((SVDBScopeItem)element).getItems().size() > 0);
	}

	@Override
	public Object[] getElements(Object element) {
		if (element instanceof SVDBScopeItem) {
			return ((SVDBScopeItem)element).getItems().toArray();
		} else {
			return new Object[0];
		}
	}

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fRoot = null;
		
		if (newInput instanceof SVDBScopeItem) {
			fRoot = (SVDBScopeItem)newInput;
		}
	}
}

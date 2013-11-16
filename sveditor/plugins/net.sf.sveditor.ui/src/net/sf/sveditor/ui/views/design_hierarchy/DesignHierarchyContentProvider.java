package net.sf.sveditor.ui.views.design_hierarchy;

import net.sf.sveditor.core.design_hierarchy.DesignHierarchyContentProviderBase;
import net.sf.sveditor.core.design_hierarchy.DesignHierarchyNode;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class DesignHierarchyContentProvider extends
		DesignHierarchyContentProviderBase implements ITreeContentProvider {

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}

	@Override
	public Object[] getElements(Object inputElement) {
		Object ret[] = new Object[fRootMap.keySet().size()];
	
		int i=0;
		for (IProject p : fRootMap.keySet()) {
			ret[i++] = p;
		}
		
		return ret;
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof DesignHierarchyNode) {
			return ((DesignHierarchyNode)element).getParent();
		} 

		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

}

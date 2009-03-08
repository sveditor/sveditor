package net.sf.sveditor.ui.editor.actions;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.utils.SVDBIndexSearcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVClassHierarchyCP implements ITreeContentProvider {
	
	private SVDBIndexSearcher				fIndexSearcher;
	private SVDBModIfcClassDecl				fLeafClass;
	private Object							fEmptyList[] = new Object[0];
	
	public SVClassHierarchyCP(
			SVDBModIfcClassDecl		leaf_class,
			SVDBIndexSearcher		index_searcher) {
		fLeafClass = leaf_class;
		fIndexSearcher = index_searcher;
	}

	public Object[] getElements(Object inputElement) {
		List<SVDBModIfcClassDecl> ret = new ArrayList<SVDBModIfcClassDecl>();

		SVDBModIfcClassDecl cl = fLeafClass;

		while (cl != null) {
			cl = fIndexSearcher.findSuperClass(cl);
			
			if (cl != null) {
				ret.add(cl);
			}
		}

		return ret.toArray();
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof SVDBModIfcClassDecl) {
			List<SVDBItem> ret = SVDBSearchUtils.findItemsByType(
					(SVDBModIfcClassDecl)parentElement,
					SVDBItemType.Function, SVDBItemType.Task);
			
			return ret.toArray();
		} else {
			return fEmptyList;
		}
	}
	

	public Object getParent(Object element) {
		return ((SVDBItem)element).getParent();
	}

	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}


	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

}

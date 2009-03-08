package net.sf.sveditor.ui.editor.actions;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.utils.SVDBIndexSearcher;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.CheckedTreeSelectionDialog;

public class OverrideMethodsDialog extends CheckedTreeSelectionDialog { 
	
	private SVDBModIfcClassDecl				fLeafClass;
	private CheckboxTreeViewer				fCheckboxTree;
	
	
	public OverrideMethodsDialog(
			Shell						parent,
			SVDBModIfcClassDecl			leaf_class,
			SVDBIndexSearcher			index_searcher) {
		super(parent, new SVTreeLabelProvider(), 
		new OverrideMethodsContentProvider(leaf_class, index_searcher));

		fLeafClass     = leaf_class;
		setInput(fLeafClass);
		updateOKStatus();
	}

	@Override
	protected CheckboxTreeViewer createTreeViewer(Composite parent) {
		fCheckboxTree =  super.createTreeViewer(parent);
		
		fCheckboxTree.addCheckStateListener(new ICheckStateListener() {

			public void checkStateChanged(CheckStateChangedEvent event) {
				if (event.getElement() instanceof SVDBModIfcClassDecl) {
					ITreeContentProvider cp = (ITreeContentProvider)
						fCheckboxTree.getContentProvider();

					boolean any_checked = false;
					for (Object c : cp.getChildren(event.getElement())) {
						if (fCheckboxTree.getChecked(c)) {
							any_checked = true;
							break;
						}
					}
					
					for (Object c : cp.getChildren(event.getElement())) {
						fCheckboxTree.setChecked(c, !any_checked); 
					}
					
					if (any_checked) {
						fCheckboxTree.setChecked(event.getElement(), !any_checked);
					}
				}
			}
			
		});
		
		fCheckboxTree.setSorter(new OverrideMethodsSorter());
		
		return fCheckboxTree;
	}
	
	
	/**
	 * ITreeContentProvider implementation
	 */
	
	private static class OverrideMethodsContentProvider implements ITreeContentProvider {
		private SVDBModIfcClassDecl				fLeafClass;
		private SVDBIndexSearcher				fIndexSearcher;
		private Object							fEmptyList[] = new Object[0];
		
		public OverrideMethodsContentProvider(
				SVDBModIfcClassDecl			leaf_class,
				SVDBIndexSearcher			index_searcher) {
			fLeafClass = leaf_class;
			fIndexSearcher = index_searcher;
		}
		
		
		public Object[] getElements(Object inputElement) {
			List<SVDBModIfcClassDecl> ret = new ArrayList<SVDBModIfcClassDecl>();

			SVDBModIfcClassDecl cl = fLeafClass;

			while (cl != null) {
				cl = fIndexSearcher.findSuperClass(cl);
				
				if (cl != null && classHasOverrideTargets(cl)) {
					ret.add(cl);
				}
			}

			return ret.toArray();
		}

		public Object[] getChildren(Object parentElement) {
			if (parentElement instanceof SVDBModIfcClassDecl) {
				return getClassOverrideTargets(
						(SVDBModIfcClassDecl)parentElement).toArray();
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

		private boolean classHasOverrideTargets(SVDBModIfcClassDecl cls) {
			return getClassOverrideTargets(cls).size() > 0;
		}
		
		private List<SVDBItem> getClassOverrideTargets(SVDBModIfcClassDecl cls) {
			List<SVDBItem> ret = new ArrayList<SVDBItem>();
			
			for (SVDBItem it : cls.getItems()) {
				if (it.getType() == SVDBItemType.Function ||
						it.getType() == SVDBItemType.Task) {
					SVDBTaskFuncScope tf = (SVDBTaskFuncScope)it;
					if ((tf.getAttr() & SVDBTaskFuncScope.FieldAttr_Local) == 0) {
						if (!existsInClass(it, fLeafClass)) {
							ret.add(it);
						}
					}
				}
			}
			
			return ret;
		}
		
		private boolean existsInClass(SVDBItem it, SVDBModIfcClassDecl cls) {
			
			for (SVDBItem it_t : cls.getItems()) {
				if (it_t.getName().equals(it.getName())) {
					return true;
				}
			}
			
			return false;
		}


		public void dispose() {}

		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
	}
	
	private static class OverrideMethodsSorter extends ViewerSorter {

		@Override
		public int compare(Viewer viewer, Object e1, Object e2) {
			if (e1 instanceof SVDBModIfcClassDecl) {
				SVDBModIfcClassDecl c1 = (SVDBModIfcClassDecl)e1;
				SVDBModIfcClassDecl c2 = (SVDBModIfcClassDecl)e2;
				
				if (c1.getSuperClass() != null && 
						c1.getSuperClass().equals(c2.getSuperClass())) {
					return 1;
				} else {
					return -1;
				}
			} else if (e1 instanceof SVDBTaskFuncScope) {
				SVDBTaskFuncScope f1 = (SVDBTaskFuncScope)e1;
				SVDBTaskFuncScope f2 = (SVDBTaskFuncScope)e2;
				int a1=0, a2=0, ret;
				
				if ((f1.getAttr() & SVDBTaskFuncScope.FieldAttr_Protected) != 0) {
					a1 += 10; 
				} else {
					a1 -= 10;
				}
				
				if ((f2.getAttr() & SVDBTaskFuncScope.FieldAttr_Protected) != 0) {
					a2 += 10;
				} else {
					a2 -= 10;
				}

				ret = f1.getName().compareTo(f2.getName());
				
				ret += (a1 - a2);
				
				return ret;
			} else {
				return super.compare(viewer, e1, e2);
			}
		}
	}
}

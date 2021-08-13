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


package org.eclipse.hdt.sveditor.ui.editor.actions;

import java.util.List;
import java.util.Set;

import org.eclipse.hdt.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import org.eclipse.hdt.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.srcgen.OverrideMethodsFinder;
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
	
	private SVDBClassDecl					fLeafClass;
	private CheckboxTreeViewer				fCheckboxTree;
	
	
	public OverrideMethodsDialog(
			Shell						parent,
			SVDBClassDecl				leaf_class,
			ISVDBIndexIterator			index_it) {
		super(parent, 
				new SVDBDecoratingLabelProvider(new SVTreeLabelProvider()), 
				new OverrideMethodsContentProvider(leaf_class, index_it));

		fLeafClass = leaf_class;
		setInput(fLeafClass);
		updateOKStatus();
	}

	@Override
	protected CheckboxTreeViewer createTreeViewer(Composite parent) {
		fCheckboxTree =  super.createTreeViewer(parent);
		
		fCheckboxTree.addCheckStateListener(new ICheckStateListener() {

			public void checkStateChanged(CheckStateChangedEvent event) {
				Object elem = event.getElement();

				if (elem instanceof SVDBClassDecl) {
					ITreeContentProvider cp = (ITreeContentProvider)
						fCheckboxTree.getContentProvider();
					
					boolean any_checked = false;
					for (Object c : cp.getChildren(event.getElement())) {
						if (fCheckboxTree.getChecked(c)) {
							any_checked = true;
							break;
						}
					}
				
					if (any_checked) {
						for (Object c : cp.getChildren(event.getElement())) {
							fCheckboxTree.setChecked(c, false);
						}
						fCheckboxTree.setChecked(event.getElement(), false);
					} else {
						for (Object c : cp.getChildren(event.getElement())) {
							fCheckboxTree.setChecked(c, true);
						}
						fCheckboxTree.setChecked(event.getElement(), true);
					}
				} else {
					ITreeContentProvider cp = (ITreeContentProvider)
						fCheckboxTree.getContentProvider();

					Object parent_o = cp.getParent(elem);
					
					if (parent_o != null && parent_o instanceof SVDBClassDecl) {
						// Update the check-box state
						
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
		private Object							fEmptyList[] = new Object[0];
		OverrideMethodsFinder					fMethodsFinder;
		private SVDBClassDecl					fLeafClass;
		
		public OverrideMethodsContentProvider(
				SVDBClassDecl			leaf_class,
				ISVDBIndexIterator		index_it) {
			fLeafClass     = leaf_class;
			fMethodsFinder = new OverrideMethodsFinder(leaf_class, index_it);
		}
		
		
		public Object[] getElements(Object inputElement) {
			Set<SVDBClassDecl> cls_set = fMethodsFinder.getClassSet();
			
			return cls_set.toArray();
		}

		public Object[] getChildren(Object parentElement) {
			if (parentElement instanceof SVDBClassDecl) {
				List<SVDBTask> methods = 
					fMethodsFinder.getMethods((SVDBClassDecl)parentElement);
				
				if (methods == null) {
					if (parentElement == fLeafClass) {
						return fMethodsFinder.getClassSet().toArray();
					}
					System.out.println("Class \"" + SVDBItem.getName((SVDBItemBase)parentElement) + "\" not in MethodsFinder");
					System.out.println("  LeafClass=" + SVDBItem.getName(fLeafClass));
					return fEmptyList;
				} else {
					return methods.toArray();
				}
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
	
	private static class OverrideMethodsSorter extends ViewerSorter {

		@Override
		public int compare(Viewer viewer, Object e1, Object e2) {
			if (e1 instanceof SVDBClassDecl) {
				SVDBClassDecl c1 = (SVDBClassDecl)e1;
				SVDBClassDecl c2 = (SVDBClassDecl)e2;
				
				if (c1.getSuperClass() != null && 
						c1.getSuperClass().equals(c2.getSuperClass())) {
					return 1;
				} else {
					return -1;
				}
			} else if (e1 instanceof SVDBTask) {
				SVDBTask f1 = (SVDBTask)e1;
				SVDBTask f2 = (SVDBTask)e2;
				int a1=0, a2=0, ret;
				
				if ((f1.getAttr() & SVDBTask.FieldAttr_Protected) != 0) {
					a1 += 10; 
				} else {
					a1 -= 10;
				}
				
				if ((f2.getAttr() & SVDBTask.FieldAttr_Protected) != 0) {
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

/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor.actions;

import java.util.List;

import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.srcgen.OverrideMethodsFinder;
import net.sf.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
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
	
	private SVDBClassDecl					fLeafClass;
	private CheckboxTreeViewer				fCheckboxTree;
	
	
	public OverrideMethodsDialog(
			Shell						parent,
			SVDBClassDecl				leaf_class,
			ISVDBIndexIterator			index_it) {
		super(parent, 
				new SVDBDecoratingLabelProvider(new SVTreeLabelProvider()), 
				new OverrideMethodsContentProvider(leaf_class, index_it));

		fLeafClass     = leaf_class;
		setInput(fLeafClass);
		updateOKStatus();
	}

	@Override
	protected CheckboxTreeViewer createTreeViewer(Composite parent) {
		fCheckboxTree =  super.createTreeViewer(parent);
		
		fCheckboxTree.addCheckStateListener(new ICheckStateListener() {

			public void checkStateChanged(CheckStateChangedEvent event) {
				if (event.getElement() instanceof SVDBModIfcDecl) {
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
		private Object							fEmptyList[] = new Object[0];
		OverrideMethodsFinder					fMethodsFinder;
		private SVDBClassDecl					fLeafClass;
		
		public OverrideMethodsContentProvider(
				SVDBClassDecl			leaf_class,
				ISVDBIndexIterator		index_it) {
			fMethodsFinder = new OverrideMethodsFinder(leaf_class, index_it);
		}
		
		
		public Object[] getElements(Object inputElement) {
			return fMethodsFinder.getClassSet().toArray();
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
			if (e1 instanceof SVDBModIfcDecl) {
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

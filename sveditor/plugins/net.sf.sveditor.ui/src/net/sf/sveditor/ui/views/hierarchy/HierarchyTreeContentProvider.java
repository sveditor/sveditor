/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.views.hierarchy;

import net.sf.sveditor.core.hierarchy.HierarchyTreeNode;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class HierarchyTreeContentProvider implements ITreeContentProvider {
	private static final Object 		fEmptyArray[] = new Object[0];
	
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof HierarchyTreeNode) {
			return ((HierarchyTreeNode)parentElement).getChildren().toArray();
		} else {
			return fEmptyArray;
		}
	}

	public Object getParent(Object element) {
		if (element instanceof HierarchyTreeNode) {
			return ((HierarchyTreeNode)element).getParent();
		} else {
			return null;
		}
	}

	public boolean hasChildren(Object element) {
		if (element instanceof HierarchyTreeNode) {
			return (((HierarchyTreeNode)element).getChildren().size() > 0);
		} else {
			return false;
		}
	}

	public Object[] getElements(Object inputElement) {
		if (inputElement instanceof HierarchyTreeNode) {
			return ((HierarchyTreeNode)inputElement).getChildren().toArray();
		} else {
			return fEmptyArray;
		}
	}

	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}

}

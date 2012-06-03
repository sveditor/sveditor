/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 *     Armond Paiva - repurposed from hierarchy to objects view
 ****************************************************************************/


package net.sf.sveditor.ui.views.objects;

import net.sf.sveditor.core.objects.ObjectsTreeNode;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class ObjectsViewContentProvider implements ITreeContentProvider {
	private static final Object 		fEmptyArray[] = new Object[0];
	
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof ObjectsTreeNode) {
			return ((ObjectsTreeNode)parentElement).getChildren().toArray();
		} else {
			return fEmptyArray;
		}
	}

	public Object getParent(Object element) {
		if (element instanceof ObjectsTreeNode) {
			return ((ObjectsTreeNode)element).getParent();
		} else {
			return null;
		}
	}

	public boolean hasChildren(Object element) {
		if (element instanceof ObjectsTreeNode) {
			return (((ObjectsTreeNode)element).getChildren().size() > 0);
		} else {
			return false;
		}
	}

	public Object[] getElements(Object inputElement) {
		if (inputElement instanceof ObjectsTreeNode) {
			return ((ObjectsTreeNode)inputElement).getChildren().toArray();
		} else {
			return fEmptyArray;
		}
	}

	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}

}

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


package net.sf.sveditor.ui.views.hierarchy;

import net.sf.sveditor.core.hierarchy.HierarchyTreeNode;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;

public class HierarchyTreeLabelProvider extends SVTreeLabelProvider {

	@Override
	public Image getImage(Object element) {
		if (element instanceof HierarchyTreeNode) {
			HierarchyTreeNode n = (HierarchyTreeNode)element;
			if (n.getItemDecl() != null) {
				return super.getImage(n.getItemDecl());
			} else {
				return null;
			}
		}
		return super.getImage(element);
	}

	@Override
	public StyledString getStyledText(Object element) {
		if (element instanceof HierarchyTreeNode) {
			HierarchyTreeNode n = (HierarchyTreeNode)element;
			if (n.getItemDecl() != null) {
				return super.getStyledText(n.getItemDecl());
			} else {
				return new StyledString(n.getName());
			}
		}
		return super.getStyledText(element);
	}
}

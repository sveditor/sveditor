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

import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.swt.graphics.Image;

public class HierarchyTreeLabelProvider extends SVTreeLabelProvider {

	@Override
	public Image getImage(Object element) {
		if (element instanceof HierarchyTreeNode) {
			return super.getImage(
					((HierarchyTreeNode)element).getClassDecl());
		}
		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof HierarchyTreeNode) {
			return super.getText(
					((HierarchyTreeNode)element).getClassDecl());
		}
		return super.getText(element);
	}

}

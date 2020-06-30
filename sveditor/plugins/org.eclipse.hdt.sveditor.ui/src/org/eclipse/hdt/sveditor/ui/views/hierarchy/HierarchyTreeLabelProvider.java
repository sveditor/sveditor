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


package org.eclipse.hdt.sveditor.ui.views.hierarchy;

import org.eclipse.hdt.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.hdt.sveditor.core.hierarchy.HierarchyTreeNode;
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

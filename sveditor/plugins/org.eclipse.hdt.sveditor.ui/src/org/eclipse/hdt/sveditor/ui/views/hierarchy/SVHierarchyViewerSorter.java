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

import org.eclipse.hdt.sveditor.core.hierarchy.HierarchyTreeNode;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;

public class SVHierarchyViewerSorter extends ViewerSorter {
	// private boolean			fSortByDefiningType;

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		if (e1 instanceof HierarchyTreeNode &&
				e2 instanceof HierarchyTreeNode) {
			HierarchyTreeNode h1 = (HierarchyTreeNode)e1;
			HierarchyTreeNode h2 = (HierarchyTreeNode)e2;
			
			return h1.getName().compareTo(h2.getName());
		} else {
			return super.compare(viewer, e1, e2);
		}
	}
	
}

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
 *     Armond Paiva - repurposed from hierarchy to objects view
 ****************************************************************************/


package org.eclipse.hdt.sveditor.ui.views.objects;

import org.eclipse.hdt.sveditor.core.objects.ObjectsTreeNode;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

public class SVObjectsViewerFilter extends ViewerFilter {
	private ObjectsTreeNode		fTarget;
	
	public void setTarget(ObjectsTreeNode on) {
		fTarget = on;
	}
	

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		if (fTarget == null) {
			return true;
		}
		return true;
	}
	
}

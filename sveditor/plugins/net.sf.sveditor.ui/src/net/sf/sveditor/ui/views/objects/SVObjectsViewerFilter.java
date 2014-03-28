/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

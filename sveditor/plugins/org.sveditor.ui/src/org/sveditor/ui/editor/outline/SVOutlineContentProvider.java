/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.ui.editor.outline;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.ui.svcp.SVTreeContentProvider;

import org.sveditor.core.Tuple;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.index.SVDBFilePath;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVOutlineContentProvider implements ITreeContentProvider {
	private SVOutlineContent			fContent;
	private SVTreeContentProvider		fBaseContentProvider;
	
	public SVOutlineContentProvider() {
		fBaseContentProvider = new SVTreeContentProvider();
	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fBaseContentProvider.inputChanged(viewer, oldInput, newInput);
		fContent = (SVOutlineContent)newInput;
	}

	public Object[] getElements(Object inputElement) {
		List<Object> ret = new ArrayList<Object>();
		
		if (inputElement instanceof SVOutlineContent) {
			SVOutlineContent c = (SVOutlineContent)inputElement;
			if (c.getFilePath() != null) {
				ret.add(c.getFilePath());
			}

			for (Object o : fBaseContentProvider.getElements(c.getFile())) {
				ret.add(o);
			}
		}
		
		return ret.toArray();
	}

	public Object[] getChildren(Object parent) {
		
		if (parent instanceof SVDBFilePath) {
			// Get children
			return ((SVDBFilePath)parent).getPath().toArray();
		} else if (parent instanceof ISVDBItemBase) {
			// Use existing content provider
			return fBaseContentProvider.getChildren(parent);
		}

		return new Object[0];
	}

	public Object getParent(Object element) {
		if (element instanceof Tuple) {
			return fContent.getFilePath();
		} else {
			return fBaseContentProvider.getParent(element);
		}
	}

	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

}

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
package net.sf.sveditor.ui.argfile.editor.outline;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVArgFileOutlineContentProvider implements ITreeContentProvider {
	private SVArgFileOutlineContent				fContent;
	private SVTreeContentProvider				fBaseContentProvider;
	
	public SVArgFileOutlineContentProvider() {
		fBaseContentProvider = new SVTreeContentProvider();
	}

	
	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fBaseContentProvider.inputChanged(viewer, oldInput, newInput);
		fContent = (SVArgFileOutlineContent)newInput;
	}

	@Override
	public Object[] getElements(Object inputElement) {
		List<Object> ret = new ArrayList<Object>();

		if (inputElement instanceof SVArgFileOutlineContent) {
			SVArgFileOutlineContent c = (SVArgFileOutlineContent)inputElement;
			if (c.getFilePath() != null) {
				ret.add(c.getFilePath());
			}
			
			for (Object o : fBaseContentProvider.getElements(c.getFile())) {
				ret.add(o);
			}
		}
		
		return ret.toArray();
	}

	@Override
	public Object[] getChildren(Object parent) {
		if (parent instanceof SVDBFilePath) {
			// Get children
			return ((SVDBFilePath)parent).getPath().toArray();
		} else if (parent instanceof ISVDBItemBase) {
			return fBaseContentProvider.getChildren(parent);
		}
		
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof Tuple) {
			return fContent.getFilePath();
		} else {
			return fBaseContentProvider.getParent(element);
		}
	}

	@Override
	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

}

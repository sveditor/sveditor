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
package org.sveditor.ui.content_providers;

import java.util.List;

import org.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVDBFileSystemContentProvider implements ITreeContentProvider {
	private ISVDBFileSystemProvider				fFS;

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput instanceof ISVDBFileSystemProvider) {
			fFS = (ISVDBFileSystemProvider)newInput;
		}

	}

	@Override
	public Object[] getElements(Object inputElement) {
		List<String> roots = fFS.getFiles("/");
		
		return roots.toArray();
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		List<String> children = fFS.getFiles((String)parentElement);
		
		return children.toArray();
	}

	@Override
	public Object getParent(Object element) {
		String path = (String)element;
		String ret = null;
		
		if (path.lastIndexOf('/') > 0) {
			ret = path.substring(0, path.lastIndexOf('/'));
		}
		
		return ret;
	}

	@Override
	public boolean hasChildren(Object element) {
		boolean ret = false;
		if (fFS.isDir((String)element)) {
			ret = fFS.getFiles((String)element).size() > 0;
		}
		
		return ret;
	}

}

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

import java.io.File;

import org.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

public class SVDBFileSystemLabelProvider extends LabelProvider {
	private ISVDBFileSystemProvider				fFS;
	
	public SVDBFileSystemLabelProvider(ISVDBFileSystemProvider fs) {
		fFS = fs;
	}
	
	@Override
	public Image getImage(Object element) {
		if (element instanceof String) {
			ISharedImages imgs = PlatformUI.getWorkbench().getSharedImages();
			
			String path = (String)element;
			if (fFS.isDir(path))  {
				return imgs.getImage(ISharedImages.IMG_OBJ_FOLDER);
			} else {
				IEditorDescriptor editor = PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(path);
				
				if (editor != null) {
					return editor.getImageDescriptor().createImage();
				}

				return imgs.getImage(ISharedImages.IMG_OBJ_FILE);
			}
		}

		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof String) {
			File f = new File((String)element);
			return f.getName();
		} else {
			return super.getText(element);
		}
	}
	

}

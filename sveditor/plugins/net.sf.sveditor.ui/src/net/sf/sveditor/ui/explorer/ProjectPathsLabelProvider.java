/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.dirtree.SVDBDirTreeNode;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;

public class ProjectPathsLabelProvider extends SVTreeLabelProvider {

	@Override
	public Image getImage(Object element) {
		if (element instanceof ProjectPathsData) {
			return SVUiPlugin.getImage("/icons/eview16/project_paths.gif");
		} else if (element instanceof SVDBDirTreeNode) {
			SVDBDirTreeNode n = (SVDBDirTreeNode)element;
			if (n.isDir()) {
				return SVUiPlugin.getImage("/icons/eview16/folder.gif");
			} else {
				return SVUiPlugin.getImage("/icons/vlog_16_16.gif");
			}
		} else if (element instanceof LibIndexPath || element instanceof ProjectPathsIndexEntry) {
			String type;
			if (element instanceof LibIndexPath) {
				type = ((LibIndexPath)element).getType();
			} else {
				type = ((ProjectPathsIndexEntry)element).getType();
			}
			if (type.equals(LibIndexPath.TYPE_SRC_COLLECTION)) {
				return SVUiPlugin.getImage("/icons/eview16/source_collection.gif");
			} else if (type.equals(LibIndexPath.TYPE_ARG_FILE) ||
					type.equals(LibIndexPath.TYPE_LIB_PATH)) {
				return SVUiPlugin.getImage("/icons/eview16/sv_lib.gif");
			}
		}
		return super.getImage(element);
	}
	
	@Override
	public StyledString getStyledText(Object element) {
		if (element instanceof IProjectPathsData) {
			return new StyledString(((IProjectPathsData)element).getName());
		} else if (element instanceof SVDBFile) {
			return new StyledString(((SVDBFile)element).getName());
		} else if (element instanceof SVDBDirTreeNode) {
			SVDBDirTreeNode n = (SVDBDirTreeNode)element;
			return new StyledString(n.getName());
		} else {
			return super.getStyledText(element);
		}
	}

}

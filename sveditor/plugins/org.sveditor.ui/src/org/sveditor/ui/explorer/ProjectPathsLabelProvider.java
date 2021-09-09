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


package org.sveditor.ui.explorer;

import org.sveditor.ui.SVDBIconUtils;
import org.sveditor.ui.SVUiPlugin;
import org.sveditor.ui.svcp.SVTreeLabelProvider;

import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.dirtree.SVDBDirTreeNode;
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
		} else if (element instanceof PackagesExplorerData) {
			return SVDBIconUtils.getIcon(SVDBItemType.PackageDecl);
		} else if (element instanceof ModulesExplorerData) {
			return SVDBIconUtils.getIcon(SVDBItemType.ModuleDecl);
		} else if (element instanceof ClassesExplorerData) {
			return SVDBIconUtils.getIcon(SVDBItemType.ClassDecl);
		} else if (element instanceof InterfacesExplorerData) {
			return SVDBIconUtils.getIcon(SVDBItemType.InterfaceDecl);
		} else if (element instanceof DeclCacheItem) {
			return super.getImage(((DeclCacheItem)element).getItem());
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

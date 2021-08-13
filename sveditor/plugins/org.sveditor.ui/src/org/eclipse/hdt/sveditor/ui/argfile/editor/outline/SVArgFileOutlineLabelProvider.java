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
package org.eclipse.hdt.sveditor.ui.argfile.editor.outline;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;
import org.eclipse.hdt.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import org.eclipse.hdt.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.index.SVDBFilePath;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class SVArgFileOutlineLabelProvider extends LabelProvider {
	private SVDBDecoratingLabelProvider			fBaseLabelProvider;
	
	public SVArgFileOutlineLabelProvider() {
		fBaseLabelProvider = new SVDBDecoratingLabelProvider(
				new SVTreeLabelProvider());
		
	}

	@Override
	@SuppressWarnings("unchecked")
	public Image getImage(Object element) {
		if (element instanceof SVDBFilePath) {
			return SVUiPlugin.getImage("/icons/eview16/include_hi.png");
		} else if (element instanceof Tuple) {
			Tuple<SVDBFileTree, ISVDBItemBase> t = (Tuple<SVDBFileTree, ISVDBItemBase>)element;
			
			if (t.second() != null) {
				ISVDBItemBase it = t.second();

				return fBaseLabelProvider.getImage(it);
			} else {
				// root file
				return SVUiPlugin.getImage("/icons/eview16/configs.gif");
			}
		} else {
			return fBaseLabelProvider.getImage(element);
		}
	}

	@Override
	@SuppressWarnings("unchecked")
	public String getText(Object element) {
		if (element instanceof SVDBFilePath) {
			return "Include Hierarchy";
		} else if (element instanceof Tuple) {
			Tuple<SVDBFileTree, ISVDBItemBase> it = (Tuple<SVDBFileTree, ISVDBItemBase>)element;
			String leaf = SVFileUtils.getPathLeaf(it.first().getFilePath());
			
			if (it.second() == null) {
				return "Active File (" + leaf + ")";
			} else {
				return leaf;
			}
		} else {
			return fBaseLabelProvider.getText(element);
		}
	}
	
}

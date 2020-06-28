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
package net.sf.sveditor.ui.editor.outline;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class SVOutlineLabelProvider extends LabelProvider {
	private SVDBDecoratingLabelProvider				fBaseLabelProvider;
	
	public SVOutlineLabelProvider() {
		fBaseLabelProvider = new SVDBDecoratingLabelProvider(new SVTreeLabelProvider());
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
				
				if (it.getType() == SVDBItemType.Include) {
					return SVDBIconUtils.getIcon(SVDBItemType.Include);
				} else {
					return fBaseLabelProvider.getImage(element);
				}
			} else {
				// root file
				return SVUiPlugin.getImage("/icons/vlog_16_16_indexed.gif");
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
			// Include-path hierarchy
			Tuple<SVDBFileTree, ISVDBItemBase> it = (Tuple<SVDBFileTree, ISVDBItemBase>)element;
			String leaf = SVFileUtils.getPathLeaf(it.first().getFilePath());
			
			if (it.second() == null) {
				return "Active File (" + leaf + ")";
			} else {
				
			}
			return SVFileUtils.getPathLeaf(it.first().getFilePath());
		} else {
			return fBaseLabelProvider.getText(element);
		}
	}
	
	

}

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


package org.eclipse.hdt.sveditor.ui.search;

import java.io.File;

import org.eclipse.hdt.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.jface.viewers.StyledString;

public class SVSearchTableLabelProvider extends SVTreeLabelProvider implements IStyledLabelProvider {
	
	public SVSearchTableLabelProvider() {
		fShowFunctionRetType = false;
	}
	
	public StyledString getStyledText(Object element) {
		if (element instanceof ISVDBItemBase) {
			StyledString ret = super.getStyledText(element);
			ISVDBItemBase item = (ISVDBItemBase)element;
			SVDBFile file = getFile(item);
			if (file != null) {
				String filename = new File(file.getFilePath()).getName();
				ret.append(" - ");
				ret.append(filename, StyledString.QUALIFIER_STYLER);
//				String decorated = super.getText(element) + " - " + filename;
//				ret.append(" - " + filename);
//				StyledCellLabelProvider.styleDecoratedString(decorated, StyledString.QUALIFIER_STYLER, ret);			
			}
			return ret;
		} else {
			return new StyledString(super.getText(element));
		}
	}

	private static SVDBFile getFile(ISVDBItemBase item) {
		SVDBFile ret = null;
		
		if (item instanceof ISVDBChildItem) {
			ISVDBChildItem it = (ISVDBChildItem)item;
			while (it != null) {
				if (it.getType() == SVDBItemType.File) {
					ret = (SVDBFile)it;
					break;
				} else {
					it = it.getParent();
				}
			}
		}
		return ret;
	}
	
}

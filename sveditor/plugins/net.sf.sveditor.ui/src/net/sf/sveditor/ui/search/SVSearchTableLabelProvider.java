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


package net.sf.sveditor.ui.search;

import java.io.File;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
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

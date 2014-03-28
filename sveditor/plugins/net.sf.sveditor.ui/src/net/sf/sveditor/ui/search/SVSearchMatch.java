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

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;

import org.eclipse.search.ui.text.Match;

public class SVSearchMatch extends Match {
	private SVDBFile				fFile;
	
	public SVSearchMatch(ISVDBItemBase item) {
		super(item, 0, 0);
	}
	
	public SVDBFile getFile() {
		if (fFile == null) {
			if (getElement() instanceof ISVDBChildItem) {
				ISVDBChildItem it = (ISVDBChildItem)getElement();
				while (it != null) {
					if (it.getType() == SVDBItemType.File) {
						fFile = (SVDBFile)it;
						break;
					}
					it = it.getParent();
				}
			}
		}
		return fFile;
	}
}

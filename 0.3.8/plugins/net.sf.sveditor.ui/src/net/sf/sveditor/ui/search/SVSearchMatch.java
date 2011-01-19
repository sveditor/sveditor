/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.search;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

import org.eclipse.search.ui.text.Match;

public class SVSearchMatch extends Match {
	private SVDBFile				fFile;
	
	public SVSearchMatch(SVDBItem item) {
		super(item, 0, 0);
	}
	
	public SVDBFile getFile() {
		if (fFile == null) {
			SVDBItem it = (SVDBItem)getElement();
			while (it != null) {
				if (it.getType() == SVDBItemType.File) {
					fFile = (SVDBFile)it;
					break;
				}
				it = (SVDBItem)it.getParent();
			}
		}
		return fFile;
	}
}

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


package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBFile;

public class SVDBIncludeSearch {
	
	public SVDBIncludeSearch(ISVDBIndex index) {
	}
	
	public SVDBFile findIncludedFile(String name) {
		SVDBFile ret = null;
		
		try {
			throw new Exception();
		} catch (Exception e) {
			System.out.println("[ERROR] SVDBIncludeSearch.findIncludedFile()");
			e.printStackTrace();
		}
		
		/*
		if ((ret = fIndex.findIncludedFile(name)) == null) {
			// Now try searching up
			ISVDBIndex index = fIndex.getSuperIndex();
			
			while (index != null) {
				if ((ret = index.findIncludedFile(name)) != null) {
					debug("        [FOUND]");
					break;
				}
				index = index.getSuperIndex();
			}
		}
		 */
		
		return ret;
	}
}

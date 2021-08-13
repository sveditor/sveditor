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


package org.eclipse.hdt.sveditor.core.db.index;

import org.eclipse.hdt.sveditor.core.db.SVDBFile;

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

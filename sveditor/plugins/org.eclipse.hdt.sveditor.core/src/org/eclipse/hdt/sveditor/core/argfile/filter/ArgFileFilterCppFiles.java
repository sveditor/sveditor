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
package org.eclipse.hdt.sveditor.core.argfile.filter;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFilePathStmt;

/**
 * Filters C++ files out of the argument file
 * 
 * @author ballance
 *
 */
public class ArgFileFilterCppFiles implements IArgFileFilter {
	private static final Set<String>			fCppSuffixes;
	
	static {
		fCppSuffixes = new HashSet<String>();
		fCppSuffixes.add(".cpp");
		fCppSuffixes.add(".c");
		fCppSuffixes.add(".cc");
		fCppSuffixes.add(".cxx");
	}

	public SVDBFile filter(SVDBFile in) {
		SVDBFile out = new SVDBFile(in.getFilePath());
		
		for (ISVDBChildItem item : in.getChildren()) {
			if (item.getType() == SVDBItemType.ArgFilePathStmt) {
				SVDBArgFilePathStmt path = (SVDBArgFilePathStmt)item;
				int dot_index = path.getPath().lastIndexOf('.');
				boolean add = true;
				
				if (dot_index != -1) {
					String suffix = path.getPath().substring(dot_index);
					suffix = suffix.toLowerCase();
					if (fCppSuffixes.contains(suffix)) {
						add = false;
					}
				}
				
				if (add) {
					out.addChildItem(item);
				}
			} else {
				out.addChildItem(item);
			}
		}
		
		return out;
	}

}

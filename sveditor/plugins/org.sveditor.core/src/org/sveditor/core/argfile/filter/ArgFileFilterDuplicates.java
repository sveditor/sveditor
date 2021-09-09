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
package org.sveditor.core.argfile.filter;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import org.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import org.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import org.sveditor.core.db.argfile.SVDBArgFileLibExtStmt;
import org.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import org.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;

public class ArgFileFilterDuplicates implements IArgFileFilter {

	public SVDBFile filter(SVDBFile in) {
		List<ISVDBChildItem> items = new ArrayList<ISVDBChildItem>();
		
		for (ISVDBChildItem it : in.getChildren()) {
			if (!contains(items, it)) {
				items.add(it);
			}
		}
		
		SVDBFile ret = new SVDBFile(in.getFilePath());
		
		for (ISVDBChildItem it : items) {
			ret.addChildItem(it);
		}
		
		return ret;
	}
	
	private boolean contains(List<ISVDBChildItem> items, ISVDBChildItem it) {
		for (ISVDBChildItem it_t : items) {
			if (equals(it_t, it)) {
				return true;
			}
		}
		return false;
	}
	
	private boolean equals(ISVDBChildItem it1, ISVDBChildItem it2) {
		if (it1.getClass() == it2.getClass()) {
			boolean eq = true;
			
			switch (it1.getType()) {
				case ArgFileDefineStmt: {
					SVDBArgFileDefineStmt s1 = (SVDBArgFileDefineStmt)it1;
					SVDBArgFileDefineStmt s2 = (SVDBArgFileDefineStmt)it2;
					
					if (s1.getKey() != null && s2.getKey() != null) {
						eq &= s1.getKey().equals(s2.getKey());
					}
					if (s1.getValue() == null || s2.getValue() == null) {
						eq &= (s1.getValue() == s2.getValue());
					} else {
						eq &= (s1.getValue().equals(s2.getValue()));
					}
				} break;
				
				case ArgFileIncDirStmt: {
					SVDBArgFileIncDirStmt s1 = (SVDBArgFileIncDirStmt)it1;
					SVDBArgFileIncDirStmt s2 = (SVDBArgFileIncDirStmt)it2;
					
					if (s1.getIncludePath() == null || s2.getIncludePath() == null) {
						eq &= (s1.getIncludePath() == s2.getIncludePath());
					} else {
						eq &= (s1.getIncludePath().equals(s2.getIncludePath()));
					}
				} break;
				
				case ArgFileIncFileStmt: {
					SVDBArgFileIncFileStmt s1 = (SVDBArgFileIncFileStmt)it1;
					SVDBArgFileIncFileStmt s2 = (SVDBArgFileIncFileStmt)it2;
				
					if (s1.getPath() == null || s2.getPath() == null) {
						eq &= (s1.getPath() == s2.getPath());
					} else {
						eq &= (s1.getPath().equals(s2.getPath()));
					}
					
					eq &= (s1.isRootInclude() == s2.isRootInclude());
				} break;
				
				case ArgFileLibExtStmt: {
					SVDBArgFileLibExtStmt s1 = (SVDBArgFileLibExtStmt)it1;
					SVDBArgFileLibExtStmt s2 = (SVDBArgFileLibExtStmt)it2;
					
					if (s1.getLibExtList() == null || s2.getLibExtList() == null) {
						eq &= (s1.getLibExtList() == s2.getLibExtList());
					} else {
						eq &= (s1.getLibExtList().equals(s2.getLibExtList()));
					}
				} break;
				
				case ArgFilePathStmt: {
					SVDBArgFilePathStmt s1 = (SVDBArgFilePathStmt)it1;
					SVDBArgFilePathStmt s2 = (SVDBArgFilePathStmt)it2;
				
					if (s1.getPath() == null || s2.getPath() == null) {
						eq &= (s1.getPath() == s2.getPath());
					} else {
						eq &= (s1.getPath().equals(s2.getPath()));
					}
				} break;
				
				case ArgFileSrcLibPathStmt: {
					SVDBArgFileSrcLibPathStmt s1 = (SVDBArgFileSrcLibPathStmt)it1;
					SVDBArgFileSrcLibPathStmt s2 = (SVDBArgFileSrcLibPathStmt)it2;
					
					if (s1.getSrcLibPath() == null || s2.getSrcLibPath() == null) {
						eq &= (s1.getSrcLibPath() == s2.getSrcLibPath());
					} else {
						eq &= (s1.getSrcLibPath().equals(s2.getSrcLibPath()));
					}
				} break;
			
				case ArgFileMfcuStmt: 
				case ArgFileForceSvStmt:
					break;
					
				default: {
					System.out.println(getClass().getName() + ": Unhandled type " +
							it1.getType());
					eq = false;
				}
			}
			return eq;
		}
		return false;
	}

}

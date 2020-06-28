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
package org.eclipse.hdt.sveditor.core.db.index;

public class SVDBIncFileInfo {
	private ISVDBIndex				fIndex;
	private String					fIncPath;
	private String					fIncFile;
	
	public SVDBIncFileInfo(ISVDBIndex index, String inc_path, String inc_file) {
		fIndex = index;
		fIncPath = inc_path;
		fIncFile = inc_file;
	}
	
	public String getIncPath() {
		return fIncPath;
	}
	
	public String getIncFile() {
		return fIncFile;
	}
	
	public boolean equals(Object other) {
		if (other instanceof SVDBIncFileInfo) {
			SVDBIncFileInfo i = (SVDBIncFileInfo)other;
			boolean eq = true;
		
			/*
			if (i.fIndex == null || fIndex == null) {
				eq &= (i.fIndex == fIndex);
			} else {
				eq &= i.fIndex.equals(fIndex);
			}
			 */
			
			if (i.fIncPath == null || fIncPath == null) {
				eq &= (i.fIncPath == fIncPath);
			} else {
				eq &= (i.fIncPath.equals(fIncPath));
			}
			
			if (i.fIncFile == null || fIncFile == null) {
				eq &= (i.fIncFile == fIncFile);
			} else {
				eq &= (i.fIncFile.equals(fIncFile));
			}
			
			return eq;
		} else {
			return false;
		}
	}

}

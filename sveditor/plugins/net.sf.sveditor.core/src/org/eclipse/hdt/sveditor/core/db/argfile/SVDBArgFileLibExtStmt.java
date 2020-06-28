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
package org.eclipse.hdt.sveditor.core.db.argfile;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBArgFileLibExtStmt extends SVDBArgFileStmt {
	
	public List<String>					fLibExtList;
	
	public SVDBArgFileLibExtStmt() {
		super(SVDBItemType.ArgFileLibExtStmt);
		
		fLibExtList = new ArrayList<String>();
	}
	
	public void addLibExt(String ext) {
		fLibExtList.add(ext);
	}
	
	public List<String> getLibExtList() {
		return fLibExtList;
	}
	

}

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

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBArgFilePathStmt extends SVDBArgFileStmt {
	public String					fSrcPath;
	
	public SVDBArgFilePathStmt() {
		super(SVDBItemType.ArgFilePathStmt);
	}
	
	public SVDBArgFilePathStmt(String path) {
		this();
		fSrcPath = path;
	}
	
	public void setPath(String path) {
		fSrcPath = path;
	}
	
	public String getPath() {
		return fSrcPath;
	}
	
}

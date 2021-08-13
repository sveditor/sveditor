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
package org.sveditor.core.db.argfile;

import org.sveditor.core.db.SVDBItemType;

public class SVDBArgFileSrcLibFileStmt extends SVDBArgFileStmt {
	public String				fSrcLibFile;
	
	public SVDBArgFileSrcLibFileStmt() {
		super(SVDBItemType.ArgFileSrcLibFileStmt);
	}
	
	public SVDBArgFileSrcLibFileStmt(String path) {
		this();
		fSrcLibFile = path;
	}

	public String getSrcLibFile() {
		return fSrcLibFile;
	}
	
	public void setSrcLibFile(String path) {
		fSrcLibFile = path;
	}
}

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

public class SVDBArgFileSrcLibPathStmt extends SVDBArgFileStmt {
	public String				fSrcLibPath;
	
	public SVDBArgFileSrcLibPathStmt() {
		super(SVDBItemType.ArgFileSrcLibPathStmt);
	}
	
	public SVDBArgFileSrcLibPathStmt(String path) {
		this();
		fSrcLibPath = path;
	}

	public String getSrcLibPath() {
		return fSrcLibPath;
	}
	
	public void setSrcLibPath(String path) {
		fSrcLibPath = path;
	}
}

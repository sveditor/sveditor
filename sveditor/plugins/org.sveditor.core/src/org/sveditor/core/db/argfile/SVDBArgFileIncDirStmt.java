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

public class SVDBArgFileIncDirStmt extends SVDBArgFileStmt {
	
	public String				fIncludePath;
	
	public SVDBArgFileIncDirStmt() {
		super(SVDBItemType.ArgFileIncDirStmt);
	}
	
	public SVDBArgFileIncDirStmt(String path) {
		this();
		setIncludePath(path);
	}
	
	public void setIncludePath(String path) {
		fIncludePath = path;
	}
	
	public String getIncludePath() {
		return fIncludePath;
	}

}

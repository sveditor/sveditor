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

public class SVDBArgFileIncFileStmt extends SVDBArgFileStmt {
	public String					fPath;
	public boolean					fRootInclude;
	
	public SVDBArgFileIncFileStmt() {
		super(SVDBItemType.ArgFileIncFileStmt);
	}

	public SVDBArgFileIncFileStmt(String path) {
		this();
		fPath = path;
	}
	
	public String getPath() {
		return fPath;
	}
	
	public void setPath(String path) {
		fPath = path;
	}
	
	public boolean isRootInclude() {
		return fRootInclude;
	}
	
	public void setRootInclude(boolean root) {
		fRootInclude = root;
	}
}

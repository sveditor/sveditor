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

public class SVDBArgFileDefineStmt extends SVDBArgFileStmt {
	public String				fKey;
	public String				fValue;
	
	public SVDBArgFileDefineStmt() {
		super(SVDBItemType.ArgFileDefineStmt);
	}
	
	public SVDBArgFileDefineStmt(String key, String val) {
		this();
		fKey = key;
		fValue = val;
	}

	public void setKey(String key) {
		fKey = key;
	}
	
	public String getKey() {
		return fKey;
	}
	
	public void setValue(String val) {
		fValue = val;
	}
	
	public String getValue() {
		return fValue;
	}
}

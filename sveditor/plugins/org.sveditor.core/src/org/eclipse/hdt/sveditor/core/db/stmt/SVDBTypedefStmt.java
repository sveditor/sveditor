/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.db.stmt;

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.ISVDBNamedItem;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBTypeInfo;

public class SVDBTypedefStmt extends SVDBStmt implements ISVDBNamedItem {
	public SVDBTypeInfo					fTypeInfo;
	// TODO: Add Vectored info
	
	public String							fName;
	
	public SVDBTypedefStmt() {
		super(SVDBItemType.TypedefStmt);
	}
	
	public SVDBTypedefStmt(SVDBTypeInfo type) {
		super(SVDBItemType.TypedefStmt);
		fTypeInfo = type;
	}
	
	public SVDBTypedefStmt(SVDBTypeInfo type, String name) {
		this(type);
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	@Override
	public SVDBTypedefStmt duplicate() {
		return (SVDBTypedefStmt)super.duplicate();
	}

	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
		
		SVDBTypedefStmt ot = (SVDBTypedefStmt)other;
		fTypeInfo = ot.fTypeInfo.duplicate();
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypedefStmt) {
			SVDBTypedefStmt o = (SVDBTypedefStmt)obj;
			
			if (!o.fTypeInfo.equals(fTypeInfo)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}
	
}

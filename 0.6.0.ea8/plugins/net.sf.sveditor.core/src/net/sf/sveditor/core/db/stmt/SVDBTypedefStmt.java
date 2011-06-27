/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class SVDBTypedefStmt extends SVDBStmt implements ISVDBNamedItem {
	private SVDBTypeInfo					fTypeInfo;
	// TODO: Add Vectored info
	
	private String							fName;
	
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

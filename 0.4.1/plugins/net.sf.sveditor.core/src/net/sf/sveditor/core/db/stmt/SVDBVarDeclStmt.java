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

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBVarDeclStmt extends SVDBStmt implements ISVDBNamedItem, IFieldItemAttr {
	public static final int				VarAttr_FixedArray			= (1 << 0);
	public static final int				VarAttr_DynamicArray		= (1 << 1);
	public static final int				VarAttr_Queue				= (1 << 2);
	public static final int				VarAttr_AssocArray			= (1 << 3);
	
	protected String					fName;
	protected SVDBTypeInfo				fTypeInfo;
	protected int						fAttr;
	protected String					fArrayDim;
	
	
	public static void init() {
		SVDBStmt.registerPersistenceFactory(new ISVDBStmtPersistenceFactory() {
			
			public SVDBStmt readSVDBStmt(ISVDBChildItem parent, SVDBStmtType stmt_type,
					IDBReader reader) throws DBFormatException {
				return new SVDBVarDeclStmt(parent, stmt_type, reader);
			}
		}, SVDBStmtType.VarDecl);
	}
	
	
	public SVDBVarDeclStmt(SVDBTypeInfo type, String name, int attr) {
		this(SVDBStmtType.VarDecl, type, name, attr);
	}

	public SVDBVarDeclStmt(SVDBStmtType stmt_type, SVDBTypeInfo type, String name, int attr) {
		super(stmt_type);
		fName = name;
		fAttr = attr;
		fTypeInfo = type;
	}

	public SVDBVarDeclStmt(ISVDBChildItem parent, SVDBStmtType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);

		fName = reader.readString();
		fTypeInfo = SVDBTypeInfo.readTypeInfo(reader);
		fAttr = reader.readInt();
		fArrayDim   = reader.readString();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fName);
		writer.writeSVDBItem(fTypeInfo);
		writer.writeInt(fAttr);
		writer.writeString(fArrayDim);
	}
	
	public String getName() {
		return fName;
	}

	public String getTypeName() {
		return fTypeInfo.getName();
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public int getAttr() {
		return fAttr;
	}
	
	public void setAttr(int attr) {
		fAttr |= attr;
	}
	
	public void resetAttr(int attr) {
		fAttr = attr;
	}

	public String getArrayDim() {
		return fArrayDim;
	}
	
	public void setArrayDim(String dim) {
		fArrayDim = dim;
	}
	
	public SVDBVarDeclStmt duplicate() {
		SVDBVarDeclStmt ret = new SVDBVarDeclStmt(
				(SVDBTypeInfo)fTypeInfo.duplicate(), getName(), fAttr);
		ret.setArrayDim(getArrayDim());
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);

		fTypeInfo.init(((SVDBVarDeclStmt)other).fTypeInfo);
		
		SVDBVarDeclStmt other_v = (SVDBVarDeclStmt)other;
		fAttr = other_v.fAttr;
		fArrayDim    = other_v.fArrayDim;
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBVarDeclStmt) {
			SVDBVarDeclStmt o = (SVDBVarDeclStmt)obj;
			if (fAttr != o.fAttr) {
				return false;
			}
			
			if (fArrayDim == null || o.fArrayDim == null) {
				if (fArrayDim != o.fArrayDim) {
					return false;
				}
			} else if (!fArrayDim.equals(o.fArrayDim)) {
				return false;
			}
			
			if (fTypeInfo == null || o.fTypeInfo == null) {
				if (fTypeInfo != o.fTypeInfo) {
					return false;
				}
			} else if (!fTypeInfo.equals(o.fTypeInfo)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}

}

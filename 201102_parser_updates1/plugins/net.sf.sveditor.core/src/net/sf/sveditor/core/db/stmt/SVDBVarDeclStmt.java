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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBVarDeclStmt extends SVDBStmt implements IFieldItemAttr {
	
	protected SVDBTypeInfo				fTypeInfo;
	protected int						fFieldAttr;
	protected List<SVDBVarDeclItem>		fVarList;
	
	public static void init() {
		SVDBPersistenceReader.registerPersistenceFactory(new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type,
					IDBReader reader) throws DBFormatException {
				return new SVDBVarDeclStmt(parent, type, reader);
			}
		}, SVDBItemType.VarDeclStmt);
	}
	
	
	public SVDBVarDeclStmt(SVDBTypeInfo type, int attr) {
		this(SVDBItemType.VarDeclStmt, type, attr);
	}

	public SVDBVarDeclStmt(SVDBItemType stmt_type, SVDBTypeInfo type, int attr) {
		super(stmt_type);
		fTypeInfo = type;
		
		fVarList = new ArrayList<SVDBVarDeclItem>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBVarDeclStmt(ISVDBChildItem parent, SVDBItemType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);

		fTypeInfo = SVDBTypeInfo.readTypeInfo(reader);
		
		fVarList = (List<SVDBVarDeclItem>)reader.readItemList(this);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeSVDBItem(fTypeInfo);
		writer.writeItemList(fVarList);
	}
	
	/**
	 * Convenience method to retrieve the name of all variables declared
	 * 
	 * @param stmt
	 * @return
	 */
	public static String getName(SVDBVarDeclStmt stmt) {
		StringBuilder sb = new StringBuilder();
		
		for (SVDBVarDeclItem vi : stmt.getVarList()) {
			sb.append(vi.getName());
			sb.append(", ");
		}
		if (sb.length() > 2) {
			sb.setLength(sb.length()-2);
		}
		
		return sb.toString();
	}
	
	public String getTypeName() {
		return fTypeInfo.getName();
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public int getAttr() {
		return fFieldAttr;
	}
	
	public void setAttr(int attr) {
		fFieldAttr |= attr;
	}
	
	public void resetAttr(int attr) {
		fFieldAttr = attr;
	}
	
	public List<SVDBVarDeclItem> getVarList() {
		return fVarList;
	}
	
	public void addVar(SVDBVarDeclItem item) {
		item.setParent(this);
		fVarList.add(item);
	}
	
	public SVDBVarDeclStmt duplicate() {
		SVDBVarDeclStmt ret = new SVDBVarDeclStmt((SVDBTypeInfo)fTypeInfo.duplicate(), fFieldAttr);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);

		fTypeInfo.init(((SVDBVarDeclStmt)other).fTypeInfo);
		
		SVDBVarDeclStmt other_v = (SVDBVarDeclStmt)other;
		fFieldAttr = other_v.fFieldAttr;
		
		fVarList.clear();
		for (SVDBVarDeclItem v : other_v.getVarList()) {
			fVarList.add(v.duplicate());
		}
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBVarDeclStmt) {
			SVDBVarDeclStmt o = (SVDBVarDeclStmt)obj;
			if (fFieldAttr != o.fFieldAttr) {
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

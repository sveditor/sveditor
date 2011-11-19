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
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class SVDBVarDeclStmt extends SVDBStmt implements IFieldItemAttr, ISVDBChildParent {
	
	protected SVDBTypeInfo				fTypeInfo;
	protected int						fFieldAttr;
	protected List<SVDBVarDeclItem>		fVarList;

	public SVDBVarDeclStmt() {
		super(SVDBItemType.VarDeclStmt);
	}
	
	public SVDBVarDeclStmt(SVDBTypeInfo type, int attr) {
		this(SVDBItemType.VarDeclStmt, type, attr);
	}

	public SVDBVarDeclStmt(SVDBItemType stmt_type, SVDBTypeInfo type, int attr) {
		super(stmt_type);
		fTypeInfo = type;
		
		fVarList = new ArrayList<SVDBVarDeclItem>();
	}
	
	/**
	 * Convenience method to retrieve the name of all variables declared
	 * 
	 * @param stmt
	 * @return
	 */
	public static String getName(SVDBVarDeclStmt stmt) {
		StringBuilder sb = new StringBuilder();
		
		for (ISVDBChildItem vi : stmt.getChildren()) {
			sb.append(SVDBItem.getName(vi));
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
	
	public void setTypeInfo(SVDBTypeInfo ti) {
		fTypeInfo = ti;
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
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fVarList.add((SVDBVarDeclItem)item);
	}

	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fVarList.iterator();
			}
		};
	}

	public SVDBVarDeclStmt duplicate() {
		return (SVDBVarDeclStmt)super.duplicate();
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

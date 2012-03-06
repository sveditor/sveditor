/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBVarDeclItem extends SVDBStmt implements ISVDBNamedItem {
	
	public String					fName;
	public int						fAttr;
	public int						fVarAttr;
	public List<SVDBVarDimItem>		fArrayDim;
	public SVDBExpr					fInitExpr;
	
	public SVDBVarDeclItem() {
		super(SVDBItemType.VarDeclItem);
	}
	
	public SVDBVarDeclItem(String name) {
		super(SVDBItemType.VarDeclItem);
		fName = name;
	}

	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setInitExpr(SVDBExpr expr) {
		fInitExpr = expr;
	}
	
	public SVDBExpr getInitExpr() {
		return fInitExpr;
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

	public List<SVDBVarDimItem> getArrayDim() {
		return fArrayDim;
	}
	
	public void setArrayDim(List<SVDBVarDimItem> dim) {
		fArrayDim = dim;
	}
	
	public SVDBVarDeclStmt getParent() {
		return (SVDBVarDeclStmt)fParent;
	}

	public void setParent(ISVDBChildItem parent) {
		fParent = (SVDBVarDeclStmt)parent;
	}

	public SVDBVarDeclItem duplicate() {
		return (SVDBVarDeclItem)super.duplicate();
	}

	public void init(ISVDBItemBase other) {
		// TODO Auto-generated method stub

	}

	public boolean equals(ISVDBItemBase other, boolean recurse) {
		// TODO Auto-generated method stub
		return false;
	}

}

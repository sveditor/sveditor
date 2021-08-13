/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.db.stmt;

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

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
		fParent = parent;
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

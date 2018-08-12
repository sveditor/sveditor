/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;

public class SVDBTask extends SVDBScopeItem implements IFieldItemAttr {
	private SVDBTFParamList					fParams;
	public int								fAttr;
	
	public SVDBTask() {
		super("", SVDBItemType.Task);
	}
	
	public SVDBTask(String name, SVDBItemType type) {
		super(name, type);
		fParams = new SVDBTFParamList();
	}

	public void setAttr(int attr) {
		fAttr = attr;
	}
	
	public int getAttr() {
		return fAttr;
	}
	
	public void addParam(SVDBParamPortDecl p) {
		fParams.addChildItem(p);
	}
	
	public SVDBTFParamList getParams() {
		return fParams;
	}
	
	public void setParams(SVDBTFParamList params) {
		fParams = params;
		fParams.setParent(this);
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);

		fAttr = ((SVDBTask)other).fAttr;
//		fParams.clear();
//		for (SVDBParamPortDecl p : ((SVDBTask)other).fParams) {
//			fParams.add((SVDBParamPortDecl)p.duplicate());
//		}
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTask) {
			boolean ret = super.equals(obj);
			SVDBTask o = (SVDBTask)obj;

			if (o.fName == null || fName == null) {
				ret &= (o.fName == fName);
			} else {
				ret &= o.fName.equals(fName);
			}

			return ret;
		}
		return false;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_task(this);
	}

	
}

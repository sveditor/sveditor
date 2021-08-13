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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.expr.SVDBExpr;

public class SVDBBind extends SVDBChildItem implements ISVDBAddChildItem, ISVDBNamedItem {
	public SVDBExpr			fTargetTypeName;
	public List<SVDBExpr>	fTargetInstNameList;
	public SVDBModIfcInst	fBindInst;
	
	public SVDBBind() {
		super(SVDBItemType.Bind);
		fTargetInstNameList = new ArrayList<SVDBExpr>();
	}
	
	public String getName() {
		return fTargetTypeName.toString();
	}
	
	public void setTargetTypeName(SVDBExpr name) {
		fTargetTypeName = name;
	}
	
	public SVDBExpr getTargetTypeName() {
		return fTargetTypeName;
	}
	
	public List<SVDBExpr> getTargetInstNameList() {
		return fTargetInstNameList;
	}
	
	public void addTargetInstName(SVDBExpr name) {
		fTargetInstNameList.add(name);
	}
	
	public void setBindInst(SVDBModIfcInst inst) {
		fBindInst = inst;
	}
	
	public SVDBModIfcInst getBindInst() {
		return fBindInst;
	}

	public void addChildItem(ISVDBChildItem item) {
		if (item instanceof SVDBModIfcInst) {
			fBindInst = (SVDBModIfcInst)item;
		} else {
			fBindInst = null;
		}
	}
}

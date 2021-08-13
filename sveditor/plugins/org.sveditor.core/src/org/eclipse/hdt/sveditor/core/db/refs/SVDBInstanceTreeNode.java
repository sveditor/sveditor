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
package org.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBModIfcInst;
import org.sveditor.core.db.SVDBModIfcInstItem;
import org.sveditor.core.db.SVDBModuleDecl;

public class SVDBInstanceTreeNode {
	private SVDBInstanceTreeNode		fParent;
	private ISVDBItemBase				fItem;
	private List<SVDBInstanceTreeNode>	fInstantiations;
	
	public SVDBInstanceTreeNode(ISVDBItemBase item) {
		fParent = null;
		fItem = item;
		fInstantiations = new ArrayList<SVDBInstanceTreeNode>();
	}
	
	public String getTypename() {
		if (fItem.getType() == SVDBItemType.ModuleDecl) {
			return ((SVDBModuleDecl)fItem).getName();
		} else if (fItem.getType() == SVDBItemType.ModIfcInstItem) {
			SVDBModIfcInst inst = (SVDBModIfcInst)((SVDBModIfcInstItem)fItem).getParent();
			return inst.getTypeName();
		} else {
			return null;
		}
	}
	
	public String getInstname() {
		if (fItem.getType() == SVDBItemType.ModIfcInstItem) {
			return ((SVDBModIfcInstItem)fItem).getName();
		}
		return null;
	}
	
	public List<SVDBInstanceTreeNode> getInstantiations() {
		return fInstantiations;
	}
	
	public SVDBInstanceTreeNode getParent() {
		return fParent;
	}
	
	public void setParent(SVDBInstanceTreeNode p) {
		fParent = p;
	}
	
	public void addInstantiation(SVDBInstanceTreeNode inst) {
		inst.setParent(this);
		fInstantiations.add(inst);
	}
	

}

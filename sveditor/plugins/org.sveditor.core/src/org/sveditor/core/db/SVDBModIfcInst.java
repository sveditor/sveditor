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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


public class SVDBModIfcInst extends SVDBFieldItem implements ISVDBChildParent {
	
	public SVDBTypeInfo				fTypeInfo;
	public List<SVDBModIfcInstItem>	fInstList;
	
	public SVDBModIfcInst() {
		super("", SVDBItemType.ModIfcInst);
		fInstList = new ArrayList<SVDBModIfcInstItem>();
	}
	
	public SVDBModIfcInst(SVDBTypeInfo type) {
		super("", SVDBItemType.ModIfcInst);
		fTypeInfo = type;
		fInstList = new ArrayList<SVDBModIfcInstItem>();
	}
	
	public List<SVDBModIfcInstItem> getInstList() {
		return fInstList;
	}
	
	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fInstList.iterator();
			}
		};
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fInstList.add((SVDBModIfcInstItem)item);
	}

	public void addInst(SVDBModIfcInstItem item) {
		item.setParent(this);
		fInstList.add(item);
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public String getTypeName() {
		if (fTypeInfo == null) {
			return "NULL";
		} else {
			return fTypeInfo.getName();
		}
	}
	
	public SVDBModIfcInst duplicate() {
		return (SVDBModIfcInst)super.duplicate();
	}
	
}

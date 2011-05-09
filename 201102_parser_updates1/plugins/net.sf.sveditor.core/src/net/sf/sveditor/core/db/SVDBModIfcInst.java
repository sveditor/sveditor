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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


public class SVDBModIfcInst extends SVDBFieldItem implements ISVDBChildParent {
	
	private SVDBTypeInfo				fTypeInfo;
	private List<SVDBModIfcInstItem>	fInstList;
	
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
	
	@SuppressWarnings("unchecked")
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
	
	public void init(ISVDBItemBase other) {
		super.init(other);
		
		SVDBModIfcInst o = (SVDBModIfcInst)other;
		if (o.fTypeInfo == null) {
			fTypeInfo = null; 
		} else {
			fTypeInfo = o.fTypeInfo.duplicate();
		}
	}
}

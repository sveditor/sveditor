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


package net.sf.sveditor.core.db;


/**
 * 
 * @author ballance
 *
 */
public class SVDBTypeInfoClassItem extends SVDBTypeInfo {
	public SVDBParamValueAssignList			fParamAssign;
	
	public SVDBTypeInfoClassItem() {
		this("");
	}
	
	public SVDBTypeInfoClassItem(String name) {
		super(name, SVDBItemType.TypeInfoClassItem);
	}

	public SVDBTypeInfoClassItem(String name, SVDBItemType type) {
		super(name, type);
	}

	public boolean hasParameters() {
		return (fParamAssign != null && fParamAssign.getParameters().size() > 0);
	}
	
	public void setParamAssignList(SVDBParamValueAssignList assign) {
		fParamAssign = assign;
	}
	
	public SVDBParamValueAssignList getParamAssignList() {
		return fParamAssign;
	}
	
	public void init_class_item(SVDBTypeInfoClassItem item) {
		setName(item.getName());
		if (item.fParamAssign == null) {
			fParamAssign = null;
		} else {
			fParamAssign = item.fParamAssign.duplicate();
		}
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_type_info_class_item(this);
	}
	
}

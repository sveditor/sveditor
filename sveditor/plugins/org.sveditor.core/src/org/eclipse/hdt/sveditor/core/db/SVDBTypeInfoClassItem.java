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


package org.eclipse.hdt.sveditor.core.db;


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
}

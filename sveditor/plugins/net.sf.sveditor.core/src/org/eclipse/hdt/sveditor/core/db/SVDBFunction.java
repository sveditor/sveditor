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


public class SVDBFunction extends SVDBTask {
	public SVDBTypeInfo				fRetType;

	public SVDBFunction() {
		super("", SVDBItemType.Function);
	}
	
	public SVDBFunction(String name, SVDBTypeInfo ret_type) {
		super(name, SVDBItemType.Function);
		fRetType = ret_type;
	}

	public SVDBTypeInfo getReturnType() {
		return fRetType;
	}
	
	public void setReturnType(SVDBTypeInfo ret) {
		fRetType = ret;
	}

	@Override
	public SVDBFunction duplicate() {
		return (SVDBFunction)super.duplicate();
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBFunction o = (SVDBFunction)other;
		fRetType = o.fRetType.duplicate(); 
	}
	
}

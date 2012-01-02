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


public class SVDBFunction extends SVDBTask {
	SVDBTypeInfo				fRetType;

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

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

public class SVDBTypeInfoModuleIfc extends SVDBTypeInfoUserDef {
	
	public SVDBTypeInfoModuleIfc() {
		super("", SVDBItemType.TypeInfoModuleIfc);
	}
	
	public SVDBTypeInfoModuleIfc(String name) {
		super(name, SVDBItemType.TypeInfoModuleIfc);
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_type_info_module_ifc(this);
	}

}

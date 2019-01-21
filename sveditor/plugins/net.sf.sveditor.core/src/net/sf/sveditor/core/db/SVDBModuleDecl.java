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

public class SVDBModuleDecl extends SVDBModIfcDecl {
	
	public SVDBModuleDecl() {
		super("", SVDBItemType.ModuleDecl);
	}
	
	public SVDBModuleDecl(String name) {
		super(name, SVDBItemType.ModuleDecl);
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_mod_ifc_decl(this);
	}
}


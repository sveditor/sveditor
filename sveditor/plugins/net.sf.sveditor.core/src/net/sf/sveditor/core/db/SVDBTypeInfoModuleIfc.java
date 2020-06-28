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


package net.sf.sveditor.core.db;

public class SVDBTypeInfoModuleIfc extends SVDBTypeInfoUserDef {
	
	public SVDBTypeInfoModuleIfc() {
		super("", SVDBItemType.TypeInfoModuleIfc);
	}
	
	public SVDBTypeInfoModuleIfc(String name) {
		super(name, SVDBItemType.TypeInfoModuleIfc);
	}

}

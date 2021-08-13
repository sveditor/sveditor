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
package org.eclipse.hdt.sveditor.core.db.vhdl;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBScopeItem;

public class VHEntityDecl extends SVDBScopeItem {
	
	public VHEntityDecl(String name) {
//		super(name, SVDBItemType.VHEntityDecl);
		super(name, SVDBItemType.ModuleDecl);
	}

}

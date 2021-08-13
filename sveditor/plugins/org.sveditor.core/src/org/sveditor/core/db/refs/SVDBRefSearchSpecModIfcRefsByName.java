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
package org.sveditor.core.db.refs;

import java.util.Stack;

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBItemType;


/**
 * Finds references to modules or interfaces
 * 
 * @author ballance
 *
 */
public class SVDBRefSearchSpecModIfcRefsByName extends SVDBRefSearchSpecByNameBase {
	
	public SVDBRefSearchSpecModIfcRefsByName(String name) {
		super(name, NameMatchType.Equals);
	}
	
	public SVDBRefSearchSpecModIfcRefsByName(String name, NameMatchType type) {
		super(name, type);
	}


	@Override
	public boolean matches(
			long		 			loc, 
			SVDBRefType 			type,
			Stack<ISVDBItemBase> 	scope, 
			String 					name) {
		if (scope.peek().getType() == SVDBItemType.ModIfcInst) {
			switch (fMatchType) {
				case MayContain:
				case Any: return true;
				case Equals: return fName.equals(name);
			}
		}
			
		return false;
	}

}

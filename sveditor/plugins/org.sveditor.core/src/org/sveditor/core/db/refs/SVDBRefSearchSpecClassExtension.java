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
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBItemType;

public class SVDBRefSearchSpecClassExtension extends
		SVDBRefSearchSpecByNameBase {
	private SVDBClassDecl			fCls;
	
	public SVDBRefSearchSpecClassExtension(SVDBClassDecl cls) {
		super(cls.getName(), NameMatchType.Equals);
		fCls = cls;
	}

	@Override
	public boolean matches(
			long		 			loc, 
			SVDBRefType 			type,
			Stack<ISVDBItemBase> 	scope, 
			String 					name) {
		if (scope.peek().getType() == SVDBItemType.ClassDecl) {
			SVDBClassDecl cls = (SVDBClassDecl)scope.peek();
			if (cls.getSuperClass() != null &&
					cls.getSuperClass().getName() != null &&
					fCls != null && fCls.getName() != null &&
					cls.getSuperClass().getName().equals(fCls.getName())) {
				return true;
			}
		}

		return false;
	}

}

/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.sveditor.core.tests;

import org.sveditor.core.db.index.ISVDBIndexIterator;

import junit.framework.TestCase;

public class SVDBIndexValidator extends TestCase {
	public static final int					ExpectErrors = (1 << 0);
	
	public void validateIndex(ISVDBIndexIterator i_it, int flags) {
	
		/** TODO:
		while (i_it.hasNext()) {
			ISVDBItemBase it = i_it.nextItem();
			assertNotNull(it);
			
			if (it.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
				for (ISVDBChildItem c : v.getChildren()) {
					SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
//					assertNotNull(v.getParent());
					assertNotNull("Parent for variable " + vi.getName() + " is null", vi.getParent());
					assertNotNull("TypeInfo for variable " + vi.getName() + " is null",
							v.getTypeInfo());
				}
			}
		}
		 */
	}
}

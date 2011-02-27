/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public class SVDBIndexValidator extends TestCase {
	public static final int					ExpectErrors = (1 << 0);
	
	public void validateIndex(ISVDBItemIterator i_it, int flags) {
		
		while (i_it.hasNext()) {
			ISVDBItemBase it = i_it.nextItem();
			
			if (SVDBStmt.isType(it, SVDBItemType.VarDeclStmt)) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
				assertNotNull("TypeInfo for variable " + 
						SVDBItem.getName(v.getParent()) + "." + v.getVarList().get(0).getName() + " is null",
						v.getTypeInfo());
			}
		}
	}
}

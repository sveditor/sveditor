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

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVScannerTests extends TestCase {
	
	public SVScannerTests() {
		
	}
	
	/**
	 * 
	 */
	public void testVariableLists() {
		LogHandle log = LogFactory.getLogHandle("testVariableLists");
		String in_data = 
			"module foo;\n" +
			"    input a, b, c, d;\n" +
			"    wire e, f, g, h;\n" + 
			"endmodule\n";
		String exp[] = {
				"input", "a",
				"input", "b",
				"input", "c",
				"input", "d",
				"wire", "e",
				"wire", "f",
				"wire", "g",
				"wire", "h"
		};
		int idx = 0;
		
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(new StringInputStream(in_data), "testVariableLists", markers);

		for (SVDBMarker m : markers) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals(1, file.getItems().size());
		assertTrue(file.getItems().get(0) instanceof SVDBModIfcDecl);
		
		SVDBModIfcDecl m = (SVDBModIfcDecl)file.getItems().get(0);
		assertEquals("foo", m.getName());
		
		for (ISVDBChildItem it : m.getChildren()) {
			assertTrue(it instanceof SVDBVarDeclStmt);
			SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
			for (SVDBVarDeclItem vi : v.getVarList()) {
				log.debug("Variable " + v.getTypeName() + " " + v.getVarList().get(0).getName());
				assertEquals(exp[idx++], v.getTypeName());
				assertEquals(exp[idx++], vi.getName());
			}
		}
		LogFactory.removeLogHandle(log);
	}
	
}

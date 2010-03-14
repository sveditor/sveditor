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
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBVarDeclItem;

public class SVScannerTests extends TestCase {
	
	public SVScannerTests() {
		
	}
	
	/**
	 * 
	 */
	public void testVariableLists() {
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
		
		SVDBFile file = SVDBFileFactory.createFile(
				new StringInputStream(in_data), "in_data");
		
		assertEquals(1, file.getItems().size());
		assertTrue(file.getItems().get(0) instanceof SVDBModIfcClassDecl);
		
		SVDBModIfcClassDecl m = (SVDBModIfcClassDecl)file.getItems().get(0);
		assertEquals("foo", m.getName());
		
		for (SVDBItem it : m.getItems()) {
			assertTrue(it instanceof SVDBVarDeclItem);
			assertEquals(exp[idx++], ((SVDBVarDeclItem)it).getTypeName());
			assertEquals(exp[idx++], ((SVDBVarDeclItem)it).getName());
		}
	}
	
}

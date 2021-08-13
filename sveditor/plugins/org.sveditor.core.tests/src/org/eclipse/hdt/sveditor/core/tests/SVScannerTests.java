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

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.StringInputStream;
import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.ISVDBFileFactory;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.SVDBModIfcDecl;
import org.sveditor.core.db.SVDBUtil;
import org.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.sveditor.core.parser.SVLanguageLevel;

import junit.framework.TestCase;

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
		
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, new StringInputStream(in_data), "testVariableLists", markers);

		for (SVDBMarker m : markers) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals(1, SVDBUtil.getChildrenSize(file));
		assertTrue(SVDBUtil.getFirstChildItem(file) instanceof SVDBModIfcDecl);
		
		SVDBModIfcDecl m = (SVDBModIfcDecl)SVDBUtil.getFirstChildItem(file);
		assertEquals("foo", m.getName());
		
		for (ISVDBChildItem it : m.getChildren()) {
			assertTrue(it instanceof SVDBVarDeclStmt);
			SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
			for (ISVDBChildItem c : v.getChildren()) {
				SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
				log.debug("Variable " + v.getTypeName() + " " + vi.getName());
				assertEquals(exp[idx++], v.getTypeName());
				assertEquals(exp[idx++], vi.getName());
			}
		}
		LogFactory.removeLogHandle(log);
	}
	
}

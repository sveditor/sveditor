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


package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseProgramBlocks extends TestCase {
	
	public void testNamedProgramBlock() {
		String doc =
			"typedef struct {\n" +
			"    int a;\n" +
			"    int b;\n" +
			"} foo_t;\n" +
			"\n" +
			"program foo_p;" +
			"\n" +
			"    always @ (a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endprogram\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testTypedPortList");
		
		for (ISVDBItemBase it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarker)it).getMessage());
			}
		}

		SVDBTestUtils.assertFileHasElements(file, "foo_p");
	}

	public void testAnonProgramBlock() {
		String doc =
			"typedef struct {\n" +
			"    int a;\n" +
			"    int b;\n" +
			"} foo_t;\n" +
			"\n" +
			"program;" +
			"\n" +
			"    always @ (a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endprogram\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testTypedPortList");
		
		for (ISVDBItemBase it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarker)it).getMessage());
			}
		}

		SVDBTestUtils.assertFileHasElements(file, "foo_t");
	}


}

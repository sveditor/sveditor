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


package org.sveditor.core.tests.parser;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBMarker;

import junit.framework.TestCase;
import org.sveditor.core.tests.SVDBTestUtils;

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
	
	public void testScopedIdentifyEndtaskTag() {
		String doc =
			"program p;\n" +
			"	class c;\n" +
			"		extern task ct ();\n" +
			"		extern task ct2 ();\n" +
			"	endclass\n" +
			"\n" +
			"	task c::ct ();\n" +
			"	endtask : c::ct\n" +
			"\n" +
			"	task c::ct2 (); // Extra indentation here caused by the :: in the line above\n" +
			"	endtask : c::ct2\n" +
			"\n" +
			"endprogram\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		
//		for (ISVDBItemBase it : file.getItems()) {
//			if (it.getType() == SVDBItemType.Marker) {
//				System.out.println("Marker: " + ((SVDBMarker)it).getMessage());
//			}
//		}

		SVDBTestUtils.assertFileHasElements(file, "p", "c", "c::ct", "c::ct2");		
	}


}

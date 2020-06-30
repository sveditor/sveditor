/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package net.sf.sveditor.core.tests.preproc;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestConditionalEval extends TestCase {
	
	public void testIfTakenNoElse() throws SVParseException {
		String testname = "testIfTakenNoElse";
		String content =
			"`define A\n" +
			"class c;\n" +
			"`ifdef A\n" +
			"	int		a;\n" +
			"`endif\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "a"});
	}

	public void testIfTakenElse() throws SVParseException {
		String testname = "testIfTakenElse";
		String content =
			"`define A\n" +
			"class c;\n" +
			"`ifdef A\n" +
			"	int		a;\n" +
			"`else\n" +
			"	int		b;\n" +
			"`endif\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "a"});
	}

	public void testIfNotTakenElseTaken() throws SVParseException {
		String testname = "testIfNotTakenElseTaken";
		String content =
			"class c;\n" +
			"`ifdef A\n" +
			"	int		a;\n" +
			"`else\n" +
			"	int		b;\n" +
			"`endif\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "b"});
	}

	public void testIfTakenElsifNoElse() throws SVParseException {
		String testname = "testIfTakenElsifNoElse";
		String content =
			"`define A\n" +
			"class c;\n" +
			"`ifdef A\n" +
			"	int		a;\n" +
			"`elsif B\n" +
			"	int		b;\n" +
			"`endif\n" +
			"endclass\n"
			;
		runTest(testname, content, 
				new String[] {"c", "a"},
				new String[] {"b"});
	}

	public void testIfTakenElsifElse() throws SVParseException {
		String testname = "testIfTakenElsifElse";
		String content =
			"`define A\n" +
			"class c;\n" +
			"`ifdef A\n" +
			"	int		a;\n" +
			"`elsif B\n" +
			"	int		b;\n" +
			"`else\n" +
			"	int 	e;\n" +
			"`endif\n" +
			"endclass\n"
			;
		runTest(testname, content, 
				new String[] {"c", "a"},
				new String[] {"b", "e"});
	}

	public void testIfNotTakenElsifTakenElse() throws SVParseException {
		String testname = "testIfNotTakenElsifTakenElse";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"`define B\n" +
			"class c;\n" +
			"`ifdef A\n" +
			"	int		a;\n" +
			"`elsif B\n" +
			"	int		b;\n" +
			"`else\n" +
			"	int 	e;\n" +
			"`endif\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "b"});
	}

	public void testIfNotTakenElsifNotTakenElseTaken() throws SVParseException {
		String testname = "testIfNotTakenElsifNotTakenElseTaken";
		String content =
			"class c;\n" +
			"`ifdef A\n" +
			"	int		a;\n" +
			"`elsif B\n" +
			"	int		b;\n" +
			"`else\n" +
			"	int 	e;\n" +
			"`endif\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "e"});
	}
	
	public void testIfNotTakenElsifTakenPostDefine() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testIfNotTakenElsifTakenPostDefine";
		String content =
			"module top;\n" +
			"`define SOME_DEFINE 1'b1\n" +
			"`define MACRO1_REV macro1\n" +
			"`define BOB bob\n" +
			"`define JANE `BOB.the\n" +
			"`define THING2 1'b1\n" +
			"//`define THING1 1'b1\n" +
			"\n" +
			"`ifdef UNDEFINED1\n" +
			"	`define THING1 1'b0\n" +
			"`elsif BOB       // Commenting this line out makes THING3 in top.sv defined\n" +
			"	`define THING1 1'b0\n" +
			"`endif\n" + 
			"\n" +
			"`define THING3 1'b0\n" +
			"`define THING3_1 1'b0\n" +
			"`define THING3_2 1'b0\n" +
			"\n" +
			"int a = `THING3;\n" +
			"int b = `THING3_1 ;\n" +
			"endmodule\n"
			;
		runTest(testname, content, new String[] {"top", "a", "b"});
	}

	private void runTest(String testname, String data, String exp_items[]) throws SVParseException {
		runTest(testname, data, exp_items, null);
	}
	
	private void runTest(String testname, String data, String exp_items[], String unexp_items[]) throws SVParseException {
		LogHandle log = LogFactory.getLogHandle(testname);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		StringInputStream in = new StringInputStream(data);
		
		SVDBFile file = SVDBTestUtils.parse(log, in, data, markers).second();
		
		assertEquals(0, markers.size());
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		
		if (unexp_items != null) {
			SVDBTestUtils.assertFileDoesNotHaveElements(file, unexp_items);
		}
		
		LogFactory.removeLogHandle(log);
	}

}

/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.preproc;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
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

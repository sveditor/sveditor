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
package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseDpiTF extends SVCoreTestCaseBase {
	
	public void testParseEscapedCId() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"program automatic test;\n" +
			"\n" +
			"	import \"DPI-C\" \\time = function int _time (inout int tloc[4]);\n" +
			"	import \"DPI-C\" function string ctime(inout int tloc[4]);\n" +
			"\n" +
			"	initial begin\n" +
			"		int tloc[4], asc[9];\n" +
			"		string t;\n" +
			"		r = _time(tloc);\n" +
			"		t = ctime(tloc);\n" +
			"		$display(\"time = '%s'\", t);\n" +
			"	end\n" +
			"endprogram : testnull\n" +
			"\n"
			;

		ParserTests.runTestStrDoc(getName(), content, new String[] {"test"});
	}

}

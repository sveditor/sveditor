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

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestParseRandsequence extends SVCoreTestCaseBase {
	
	public void testRandsequence_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class rs1;\n" +
			"\n" +
			"	task rs_t();\n" +
			"		randsequence( main )\n" +
			"			main : first second done ;\n" +
			"			first : add | dec ;\n" +
			"			second : pop | push ;\n" +
			"			done : { $display(\"done\"); } ;\n" +
			"			add : { $display(\"add\"); } ;\n" +
			"			dec : { $display(\"dec\"); } ;\n" +
			"			pop : { $display(\"pop\"); } ;\n" +
			"			push : { $display(\"push\"); } ;\n" +
			"		endsequence\n" +
			"	endtask\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, new String[] {"rs1", "rs_t"});
	}

}

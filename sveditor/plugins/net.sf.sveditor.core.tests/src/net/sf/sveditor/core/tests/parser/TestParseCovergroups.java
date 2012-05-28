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


package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;
import junit.framework.TestCase;

public class TestParseCovergroups extends TestCase {

	  public void testCovergroup() throws SVParseException {
		String testname = "testTransitionBins";
	    SVCorePlugin.getDefault().enableDebug(true);
	    String doc =
	      "class c;\n" +
	      " covergroup foobar;\n" +
	      "   foo_cp : coverpoint (foo);\n" +
	      "   foo2_cp : coverpoint foo2;\n" +
	      "   foo_cross : cross foo_cp, foo2_cp {\n" +
	      "     ignore_bins foo = binsof(foo_cp) intersect {0};\n" +
	      "   }\n" +
	      "   foo_cross_not_bins : cross foo_cp, foo2_cp {\n" +
	      "     ignore_bins foo = !binsof(foo_cp) intersect {0};\n" +
	      "   }\n" +
	      " endgroup\n" +
	      "endclass\n"
	      ;

		ParserTests.runTestStrDoc(testname, doc, new String[] {"c","foobar"});
	  }


	public void testTransitionBins() throws SVParseException {
		String testname = "testTransitionBins";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class c;\n" +
			"	covergroup cg;\n" +
			"		a_cp : coverpoint a {\n" +
			"			bins a_bins[] = (0 => 0,1), (1 => 0);\n" +
			"		}\n" +
			"	endgroup\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"c","cg"});
	}

}

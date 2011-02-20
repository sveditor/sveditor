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


package net.sf.sveditor.core.tests.scanner;

import junit.framework.TestCase;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;

public class TestStatementScanner extends TestCase {
	
	public void testScanClassStatements() {
		String content = 
			"class __sv_builtin_covergroup_options;\n" +
			"	int 	weight;\n" + 
			"\n" +
			"	real 	goal;\n" +
			"\n" +
			"	string 	name;\n" +
			"\n" +
			"	string 	comment;\n" +
			"\n" +
			"	int		at_least;\n" +
			"\n" +
			"	bit		detect_overlap;\n" +
			"\n" +
			"	int		auto_bin_max;\n" +
			"\n" +
			"	bit		per_instance;\n" +
			"\n" +
			"	bit		cross_num_print_missing;\n" +
			"\n" +
			"endclass\n";
		String exp[] = {
				"class",
				"int",
				"real",
				"string",
				"string",
				"int",
				"bit",
				"int",
				"bit",
				"bit",
				"endclass"
		};
		int idx = 0;
		
		ParserSVDBFileFactory factory = new ParserSVDBFileFactory(null);
		factory.init(new StringInputStream(content), "content");
		
		String id;
		while ((id = factory.scan_statement()) != null) {
			if (idx >= exp.length) {
				fail("Ran out of expected data @ \"" + id + "\"");
			}
			System.out.println("id=" + id);
			assertEquals(exp[idx], id);
			idx++;
		}
		
		assertEquals(exp.length, idx);
	}

}

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
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBUtil;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseLineNumbers extends TestCase {
	
	public void testClassLineNumbers() {
		String content =
			"class foobar;\n" + 	// 1
			"    int a;\n" + 		// 2
			"    int b;\n" +		// 3
			"\n" +					// 4
			"endclass\n" +			// 5
			"\n" +					// 6
			"\n"					// 7
			;
		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
		SVDBClassDecl cls = null;

		assertEquals("Wrong number of file elements", 1, SVDBUtil.getChildrenSize(file));
		
		cls = (SVDBClassDecl)SVDBUtil.getFirstChildItem(file);
		
		assertNotNull("Start location not specified", cls.getLocation());
		assertNotNull("End location not specified", cls.getEndLocation());
		
		assertEquals("Wrong start location", 1, cls.getLocation().getLine());
		assertEquals("Wrong end location", 5, cls.getEndLocation().getLine());
	}

	public void testClassFunctionLineNumbers() {
		String content =
			"class foobar;\n" + 					// 1
			"    int a;\n" + 						// 2
			"    int b;\n" +						// 3
			"\n" +									// 4
			"    function void foobar_f();\n" + 	// 5
			"        a = 5;\n" +					// 6
			"        b = 6;\n" +					// 7
			"    endfunction\n" +					// 8
			"\n" +									// 9
			"    function void foobar_f2();\n" +	// 10
			"        a = 4;\n" +					// 11
			"        b = 12;\n" +					// 12
			"    endfunction\n" +					// 13
			"\n" +									// 14
			"endclass\n" +							// 15
			"\n" +									// 16
			"\n"									// 17
			;
		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
		SVDBClassDecl cls = null;

		assertEquals("Wrong number of file elements", 1, SVDBUtil.getChildrenSize(file));
		
		cls = (SVDBClassDecl)SVDBUtil.getFirstChildItem(file);
		
		assertNotNull("Start location not specified", cls.getLocation());
		assertNotNull("End location not specified", cls.getEndLocation());
		
		assertEquals("Wrong start location", 1, cls.getLocation().getLine());
		assertEquals("Wrong end location", 15, cls.getEndLocation().getLine());
		
		SVDBTask f1=null, f2=null;
		
		for (ISVDBItemBase it : cls.getChildren()) {
			if (SVDBItem.getName(it).equals("foobar_f")) {
				f1 = (SVDBTask)it;
			}
			if (SVDBItem.getName(it).equals("foobar_f2")) {
				f2 = (SVDBTask)it;
			}
		}
		
		assertNotNull(f1);
		assertNotNull(f2);
		assertEquals("Wrong foobar_f start location", 5, f1.getLocation().getLine());
		assertEquals("Wrong foobar_f end location", 8, f1.getEndLocation().getLine());
		
		assertEquals("Wrong foobar_f2 start location", 10, f2.getLocation().getLine());
		assertEquals("Wrong foobar_f2 end location", 13, f2.getEndLocation().getLine());
	}

}

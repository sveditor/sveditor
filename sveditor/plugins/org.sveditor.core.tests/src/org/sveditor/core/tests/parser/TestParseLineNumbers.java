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

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.SVDBTask;
import org.sveditor.core.db.SVDBUtil;

import junit.framework.TestCase;
import org.sveditor.core.tests.SVDBTestUtils;

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
		
		assertEquals("Wrong start location", 1, 
				SVDBLocation.unpackLineno(cls.getLocation()));
		assertEquals("Wrong end location", 5, 
				SVDBLocation.unpackLineno(cls.getEndLocation()));
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
		
		assertEquals("Wrong start location", 1, 
				SVDBLocation.unpackLineno(cls.getLocation()));
		assertEquals("Wrong end location", 15, 
				SVDBLocation.unpackLineno(cls.getEndLocation()));
		
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
		assertEquals("Wrong foobar_f start location", 5, 
				SVDBLocation.unpackLineno(f1.getLocation()));
		assertEquals("Wrong foobar_f end location", 8, 
				SVDBLocation.unpackLineno(f1.getEndLocation()));
		
		assertEquals("Wrong foobar_f2 start location", 10, 
				SVDBLocation.unpackLineno(f2.getLocation()));
		assertEquals("Wrong foobar_f2 end location", 13, 
				SVDBLocation.unpackLineno(f2.getEndLocation()));
	}

}

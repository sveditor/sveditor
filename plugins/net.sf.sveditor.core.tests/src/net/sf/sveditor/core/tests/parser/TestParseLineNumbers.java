package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;

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
		SVDBFile file = ParserTests.parse(content, "testClassStringFields");
		
		SVDBModIfcClassDecl cls = null;

		assertEquals("Wrong number of file elements", 1, file.getItems().size());
		
		cls = (SVDBModIfcClassDecl)file.getItems().get(0);
		
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
		SVDBFile file = ParserTests.parse(content, "testClassStringFields");
		
		SVDBModIfcClassDecl cls = null;

		assertEquals("Wrong number of file elements", 1, file.getItems().size());
		
		cls = (SVDBModIfcClassDecl)file.getItems().get(0);
		
		assertNotNull("Start location not specified", cls.getLocation());
		assertNotNull("End location not specified", cls.getEndLocation());
		
		assertEquals("Wrong start location", 1, cls.getLocation().getLine());
		assertEquals("Wrong end location", 15, cls.getEndLocation().getLine());
		
		SVDBTaskFuncScope f1=null, f2=null;
		
		for (SVDBItem it : cls.getItems()) {
			if (it.getName().equals("foobar_f")) {
				f1 = (SVDBTaskFuncScope)it;
			}
			if (it.getName().equals("foobar_f2")) {
				f2 = (SVDBTaskFuncScope)it;
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

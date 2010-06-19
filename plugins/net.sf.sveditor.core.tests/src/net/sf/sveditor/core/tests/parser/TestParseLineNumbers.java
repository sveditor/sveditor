package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;

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

}

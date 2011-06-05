package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestLexer extends TestCase {
	
	public void testSpaceContainingNumber() throws SVParseException {
		
		String content = 
			"class c;\n" +
			"	int a = 32 'h 0000_1111_2222_3333;\n" +
			"	int b = 32'h 0000_1111_2222_3333;\n" +
			"endclass\n";
		
		runTest("testSpaceContainingNumber", content, new String[] {"c", "b"});
	}

	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}
	
}

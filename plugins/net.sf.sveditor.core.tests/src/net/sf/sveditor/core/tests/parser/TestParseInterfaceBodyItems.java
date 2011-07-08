package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestParseInterfaceBodyItems extends TestCase {
	
	public void testModportBasic() throws SVParseException {
		String doc = 
			"interface foo;\n" +
			"   modport foo_m(input a, b, c, output d, e, f);\n" +
			"endinterface\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testModportBasic");
		SVDBTestUtils.assertFileHasElements(file, "foo");
	}

	public void testModportMethod() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
			"interface foo;\n" +
			"   modport foo_m(\n" +
			"		import function int get(ref int a, int b),\n" +
			"		input a, b, c, output d, e, f\n" +
			"		);\n" +
			"endinterface\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testModportBasic");
		SVDBTestUtils.assertFileHasElements(file, "foo");
	}
	
}


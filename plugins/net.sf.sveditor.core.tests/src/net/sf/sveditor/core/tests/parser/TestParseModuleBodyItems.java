package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import junit.framework.TestCase;

public class TestParseModuleBodyItems extends TestCase {
	
	public void testInitialBlock() {
		String doc =
			"module top;\n" +
			"    int a;\n" +
			"\n" +
			"    initial begin\n" +
			"        int b;\n" +
			"        b = 5;\n" +
			"        a = 6;\n" +
			"        assert(a == 6);\n" +
			"    end\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVDBFile file = ParserTests.parse(doc, "doc");
		
		SVDBModIfcClassDecl top = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("top")) {
				top = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find module top", top);
		
		SVDBScopeItem initial = null;
		for (SVDBItem it : top.getItems()) {
			if (it.getType() == SVDBItemType.InitialBlock) {
				initial = (SVDBScopeItem)it;
				break;
			}
		}
		
		assertNotNull("Failed to find initial block", initial);
	}

}

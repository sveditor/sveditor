package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
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
	
	public void testPortList() {
		String doc =
			"module top(a, b, c, d);\n" +
			"    input a;\n" +
			"    output b;\n" +
			"    input [7:0] c;\n" +
			"    output[11:0] d;\n" +
			"\n" +
			"    wire [12:0] bus;\n" +
			"\n" +
			"    always @ (a) begin\n" +
			"        b = ~a;\n" +
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
		
		SVDBItem a=null, b=null, c=null, d=null, bus=null;
		for (SVDBItem it : top.getItems()) {
			if (it.getName().equals("a")) {
				a = it;
			} else if (it.getName().equals("b")) {
				b = it;
			} else if (it.getName().equals("c")) {
				c = it;
			} else if (it.getName().equals("d")) {
				d = it;
			} else if (it.getName().equals("bus")) {
				bus = it;
			}
		}
		
		assertNotNull(a);
		assertNotNull(b);
		assertNotNull(c);
		assertNotNull(d);
		assertNotNull(bus);
		
		assertEquals("input", ((SVDBVarDeclItem)a).getTypeName());
		assertEquals("input", ((SVDBVarDeclItem)a).getTypeName());
		assertTrue((bus instanceof SVDBVarDeclItem));
		assertTrue((((SVDBVarDeclItem)bus).getTypeInfo() instanceof SVDBTypeInfoBuiltin));
		assertEquals("[12:0]", ((SVDBTypeInfoBuiltin)((SVDBVarDeclItem)bus).getTypeInfo()).getVectorDim());
	}
}

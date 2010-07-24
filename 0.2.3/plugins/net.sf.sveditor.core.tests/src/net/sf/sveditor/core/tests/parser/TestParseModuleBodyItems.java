package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
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
		
		SVDBFile file = ParserTests.parse(doc, "testInitialBlock");
		
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
			"module top(a, b, c, d);\n" +		// 1
			"    input a;\n" +					// 2
			"    output b;\n" +					// 3
			"    input [7:0] c;\n" +			// 4
			"    output[11:0] d;\n" +			// 5
			"\n" +								// 6
			"    wire [12:0] bus;\n" +			// 7
			"\n" +								// 8
			"    always @ (a) begin\n" +		// 9
			"        b = ~a;\n" +				// 10
			"    end\n" +						// 11
			"\n" +								// 12
			"endmodule\n"						// 13
			;

		SVCorePlugin.getDefault().enableDebug(true);
		SVDBFile file = ParserTests.parse(doc, "testPortList");
		
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
			}
		}

		SVDBModIfcClassDecl top = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("top")) {
				top = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find module top", top);
		
		for (SVDBParamPort p : top.getPorts()) {
			System.out.println("Port: " + p.getName());
		}

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
	
	public void testTypedPortList() {
		String doc =
			"typedef struct {\n" +
			"    int a;\n" +
			"    int b;\n" +
			"} foo_t;\n" +
			"\n" +
			"module top(\n" +
			"    input int    a,\n" +
			"    input foo_t  b,\n" +
			"    input bar[13:0]\n" +
			"    );\n" +
			"\n" +
			"    always @ (a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(true);
		SVDBFile file = ParserTests.parse(doc, "testTypedPortList");
		
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
			}
		}

		SVDBModIfcClassDecl top = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("top")) {
				top = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find module top", top);

		SVDBParamPort a=null, b=null, bar=null;
		for (SVDBParamPort p : top.getPorts()) {
			System.out.println("Port: " + p.getName());
			if (p.getName().equals("a")) {
				a = p;
			} else if (p.getName().equals("b")) {
				b = p;
			} else if (p.getName().equals("bar")) {
				bar = p;
			}
		}
		
		assertNotNull(a);
		assertNotNull(b);
		assertNotNull(bar);

		assertEquals(SVDBDataType.UserDefined, b.getTypeInfo().getDataType());
		assertEquals("foo_t", ((SVDBTypeInfoUserDef)b.getTypeInfo()).getName());
	}

	public void testAlwaysBlock() {
		String doc =
			"module top;\n" +
			"\n" +
			"    always @ (posedge a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(true);
		SVDBFile file = ParserTests.parse(doc, "testAlwaysBlock");
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
				SVDBMarkerItem m = (SVDBMarkerItem)it;
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
					errors.add(m);
				}
			}
		}

		SVDBModIfcClassDecl top = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("top")) {
				top = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find module top", top);
		
		assertEquals("No Errors", 0, errors.size());
	}

}


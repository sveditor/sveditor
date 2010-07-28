package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltinNet;
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

		SVCorePlugin.getDefault().enableDebug(false);
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
			System.out.println("[Item] " + it.getType() + " " + it.getName());
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
		SVDBVarDeclItem v = (SVDBVarDeclItem)bus;
		System.out.println("bus.type.class=" + v.getTypeInfo().getClass().getName());
		assertTrue((((SVDBVarDeclItem)bus).getTypeInfo() instanceof SVDBTypeInfoBuiltinNet));
		SVDBTypeInfoBuiltinNet net_type = (SVDBTypeInfoBuiltinNet)((SVDBVarDeclItem)bus).getTypeInfo();
		assertEquals("[12:0]", 
				((SVDBTypeInfoBuiltin)net_type.getTypeInfo()).getVectorDim());
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

		SVCorePlugin.getDefault().enableDebug(false);
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

		SVCorePlugin.getDefault().enableDebug(false);
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

	public void testNestedModule() {
		String doc =
			"module top;\n" +
			"\n" +
			"    module inner;\n" +
			"    	always @ (posedge a) begin\n" +
			"       	 b = ~a;\n" +
			"    	end\n" +
			"    endmodule\n" +
			"\n" +
			"\n" +
			"endmodule\n"
			;

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
			}
		}
		
		assertNotNull("Failed to find module top", top);
		
		SVDBModIfcClassDecl inner = null;
		for (SVDBItem it : top.getItems()) {
			if (it.getName().equals("inner")) {
				inner = (SVDBModIfcClassDecl)it;
			}
		}

		assertNotNull("Failed to find module inner", inner);
		assertEquals("No Errors", 0, errors.size());
	}
	
	public void testEmptyParamList() {
		String doc =
			"module t2\n" +
			"#(\n" +
			");\n" +
			"endmodule";

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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl t2 = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("t2")) {
				t2 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module top", t2);
	}
	
	public void testParameterDeclaration() {
		
		String doc =
			"module t1;\n" +
			"    parameter c = 1;\n" +
			"endmodule\n"
			;

		SVDBFile file = ParserTests.parse(doc, "testParameterDeclaration");
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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl t1 = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("t1")) {
				t1 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t1", t1);
		
		SVDBParamPort c = null;
		for (SVDBItem it : t1.getItems()) {
			if (it.getName().equals("c")) {
				c = (SVDBParamPort)it;
			}
		}
		assertNotNull(c);
	}
	
	public void testOutputPort() {
		
		String doc =
			"module t4(o);\n" +
			"    output logic o;\n" +
			"endmodule\n"
			;

		SVDBFile file = ParserTests.parse(doc, "testTypedInitializedParameterDecl");
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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl t4 = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("t4")) {
				t4 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t4", t4);
	}

	public void testUntypedInputPort() {
		
		String doc =
			"module t\n" +
			"(\n" +
			"output logic [3:0] out,\n" +
			"input logic [1:0] in,\n" +
			"input [1:0] in2\n" +
			");\n" +
			"endmodule\n"
			;

		SVDBFile file = ParserTests.parse(doc, "testUntypedInputPort");
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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl t = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("t")) {
				t = (SVDBModIfcClassDecl)it;
			}
		}
		assertNotNull("Failed to find module t", t);
		
		SVDBParamPort out=null, in=null, in2=null;
		
		for (SVDBParamPort p : ((SVDBModIfcClassDecl)t).getPorts()) {
			if (p.getName().equals("out")) {
				out = p;
			} else if (p.getName().equals("in")) {
				in = p;
			} else if (p.getName().equals("in2")) {
				in2 = p;
			}
		}
		assertNotNull("Failed to find \"out\"", out);
		assertNotNull("Failed to find \"in\"", in);
		assertNotNull("Failed to find \"in2\"", in2);
	}

	public void testTypedInitializedParameterDecl() {
		
		String doc =
			"module t3\n" +
			"#(\n" +
			"parameter int c [0:1] = '{0, 1}\n" +
			");\n" +
			"endmodule\n";			

		SVDBFile file = ParserTests.parse(doc, "testTypedInitializedParameterDecl");
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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl t2 = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("t3")) {
				t2 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t3", t2);
	}

	public void testMappedParameterizedModule() {
		
		String doc =
			"module t5;\n" +
			"    Abc #(1, 2) abc(out, in);\n" +
			"    Abc #(.p(1), .p2(2)) abc2(out, in);\n" +
			"endmodule\n"
			;

		SVDBFile file = ParserTests.parse(doc, "testMappedParameterizedModule");
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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl t5 = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("t5")) {
				t5 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t5", t5);
	}

	public void testGlobalParamRef() {
		
		String doc =
			"parameter int c [0:1] = '{0, 1};\n" +
			"	module t6\n" +
			"	#(\n" +
			"	parameter c2 = c[0]\n" +
			"	);\n" +
			"	endmodule\n"
			;
			
		SVDBFile file = ParserTests.parse(doc, "testMappedParameterizedModule");
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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl t6 = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("t6")) {
				t6 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t6", t6);
	}


	public void testVarCompare() {
		String doc = 
			"module HalfSeTable(sIdx, LutIndex);\n" +
			"	// Optimize the table size by the sorting stage index.\n" +
			"	parameter sortId = 0;\n" +
			"	output logic [sortId*3-1:0] sIdx;\n" +
			"	input [2:0] LutIndex;\n" +
			"\n" +
			"	// Half SE table. Symbols are 802.11 Gray-encoded.\n" +
			"	always@(LutIndex) begin\n" +
			"		case(LutIndex)\n" +
			"    	// SE order:    (best)7   5   3   1  -1  -3  -5  -7\n" +
			"		3'b000: sIdx = (24'b100_101_111_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b001: sIdx = (24'b100_101_111_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b010: sIdx = (24'b101_100_111_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b011: sIdx = (24'b101_111_100_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b100: sIdx = (24'b111_101_110_100_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b101: sIdx = (24'b111_110_101_010_100_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b110: sIdx = (24'b110_111_010_101_011_100_001_000)>>((8-sortId)*3);\n" +
			"		3'b111: sIdx = (24'b110_010_111_011_101_001_100_000)>>((8-sortId)*3);\n" +
			"		endcase\n" +
			"	end\n" +
			"endmodule\n";

		SVDBFile target_file = new SVDBFile("testMappedParameterizedModule");
		SVDBFile file = ParserTests.parse(doc, "testMappedParameterizedModule");
		
		SVDBFileMerger.merge(target_file, file, null, null, null);
		
		// Merge twice for good measure. The first time actually does something.
		// The second time ensures maximum compares
		SVDBFileMerger.merge(target_file, file, null, null, null);
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
		
		assertEquals("Encountered errors", 0, errors.size());

		SVDBModIfcClassDecl HalfSeTable = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("HalfSeTable")) {
				HalfSeTable = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module HalfSeTable", HalfSeTable);
	}

}


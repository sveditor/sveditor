package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;

public class TestParseProgramBlocks extends TestCase {
	
	public void testNamedProgramBlock() {
		String doc =
			"typedef struct {\n" +
			"    int a;\n" +
			"    int b;\n" +
			"} foo_t;\n" +
			"\n" +
			"program foo_p;" +
			"\n" +
			"    always @ (a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endprogram\n"
			;

		SVCorePlugin.getDefault().enableDebug(true);
		SVDBFile file = ParserTests.parse(doc, "testTypedPortList");
		
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
			}
		}

		SVDBModIfcClassDecl foo_p = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("foo_p")) {
				foo_p = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find program foo_p", foo_p);
	}

	public void testAnonProgramBlock() {
		String doc =
			"typedef struct {\n" +
			"    int a;\n" +
			"    int b;\n" +
			"} foo_t;\n" +
			"\n" +
			"program;" +
			"\n" +
			"    always @ (a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endprogram\n"
			;

		SVCorePlugin.getDefault().enableDebug(true);
		SVDBFile file = ParserTests.parse(doc, "testTypedPortList");
		
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
			}
		}

		SVDBModIfcClassDecl foo_p = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Program) {
				foo_p = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find program foo_p", foo_p);
	}


}

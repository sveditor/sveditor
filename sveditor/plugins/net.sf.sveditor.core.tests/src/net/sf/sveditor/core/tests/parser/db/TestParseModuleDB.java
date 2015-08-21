package net.sf.sveditor.core.tests.parser.db;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseModuleDB extends SVCoreTestCaseBase {
	
	public void testPortWidth() {
		String content =
			"module top(\n" +
			"	output wire[31:0] a_misc,\n" +
			"   input retain_ctrl,\n" +
			"	input save_sel,\n" +
			"	input save_ctrl);\n" +
			"endmodule\n"
			;
			
			
		
		SVDBFile file = SVDBTestUtils.parse(content, "foo.bar");
		
		SVDBModuleDecl m = (SVDBModuleDecl)file.getChildren().iterator().next();
		
		SVDBParamPortDecl p0 = m.getPorts().get(0);
		SVDBParamPortDecl p1 = m.getPorts().get(1);

		assertEquals("wire[31:0]", p0.getTypeInfo().toString());
		assertEquals("wire", p1.getTypeInfo().toString());

	}

}

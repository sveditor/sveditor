package net.sf.sveditor.core.tests.checker;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;

public class TestCheckMethods extends TestCase {
	
	public void testUnknownVarRef() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(true);
		
		String content = 
				"class cls;\n"							// 1
				+ "int  m_field;\n"
				+ "\n"
				+ "  function void doit();\n"
				+ "		for (i=0; i<16; i++) begin\n"	// 5
				+ "			m_field++;\n"
				+ "		end\n" 
				+ "  endfunction\n"						// 8
				+ "endclass\n"
				;
		
		CheckerTests.runTest(getName(), content,
				"5:i cannot be resolved to a variable"
				);
	}

}

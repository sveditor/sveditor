package net.sf.sveditor.vhdl.core.tests.index;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.vhdl.core.parser.VhdlFileFactory;
import net.sf.sveditor.vhdl.core.tests.VhdlCoreTestCase;

public class TestVhdlArgFileIndexBasics extends VhdlCoreTestCase {
	
	public void testBasicParse() {
		String input = 
				"entity foo is\n" +
				"end entity;\n"
				;
		
		VhdlFileFactory f = new VhdlFileFactory();
		
		f.parse(new StringInputStream(input));
		
	}

	public void testUARTParse() {
		String input = 
				"entity foo is\n" +
				"end entity;\n"
				;
		
		VhdlFileFactory f = new VhdlFileFactory();
		
		f.parse(new StringInputStream(input));
		
	}
	
}

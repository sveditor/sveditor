package net.sf.sveditor.vhdl.core.tests.index;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.vhdl.core.parser.VhdlFileFactory;
import net.sf.sveditor.vhdl.core.tests.VhdlCoreTestCase;

public class TestVhdlArgFileIndexBasics extends VhdlCoreTestCase {
	
	public void testBasicParse() {
		String input = 
				"package pkg is\n" +
				"  type rec_type is record\n" +
				"    addr : std_logic_vector(15 downto 0);\n" +
				"  end record;\n" +
				"end package;\n"
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

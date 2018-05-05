package net.sf.sveditor.vhdl.core.tests.index;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.vhdl.parser.VHDLFileFactory;
import net.sf.sveditor.vhdl.core.tests.VhdlCoreTestCase;

public class TestVhdlArgFileIndexBasics extends VhdlCoreTestCase {
	

	public void testSmoke() {
		String doc =
			"library ieee;\n" + 
			"    use ieee.std_logic_1164.all;\n" + 
			"\n" + 
			"entity mux_using_with is\n" + 
			"    port (\n" + 
			"        din_0   :in  std_logic; -- Mux first input\n" + 
			"        din_1   :in  std_logic; -- Mux Second input\n" + 
			"        sel     :in  std_logic; -- Select input\n" + 
			"        mux_out :out std_logic  -- Mux output\n" + 
			"\n" + 
			"    );\n" + 
			"end entity;\n" + 
			"\n" + 
			"architecture behavior of mux_using_with is\n" + 
			"\n" + 
			"begin\n" + 
			"    with (sel) select\n" + 
			"    mux_out <= din_0 when '0',\n" + 
			"               din_1 when others;\n" + 
			"        \n" + 
			"end architecture;\n"
			;
		VHDLFileFactory f = new VHDLFileFactory();
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		f.parse(new StringInputStream(doc), getName(), markers);
	}
	
}

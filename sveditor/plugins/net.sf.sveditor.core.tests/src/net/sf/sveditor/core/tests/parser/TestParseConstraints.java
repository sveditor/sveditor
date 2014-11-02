package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseConstraints extends SVCoreTestCaseBase {
	
	public void testParseConstraintFunction() {
		String doc = 
				"class bob;\n" +
				"	constraint some_constraint {\n" +
				"		if (1) {\n" +
//				"			some_variable  == some_function(.arg1(value1)); // Commenting this in or  out affects the error on the next line\n" +
				"			some_variable  == some_function(.arg1(value1), .arg2(value2));\n" +
				"		}\n" +
				"	}\n" +
				"endclass\n"
				;
	
		runTest(doc, new String[] {"bob", "some_constraint"});
	}
	
	public void testForeach() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class top;\n" +
			"	constraint some_const {\n" +
			"		if (thing.opcode inside {thingy::SFR_WR, \n" +
			"			thingy::SFR_RD,\n" +
			"			thingy::SFR_BIT_SET,\n" +
			"			thingy::SFR_BIT_CLR,\n" +
			"			thingy::SFR_BIT_INV\n" +
			"			}) {\n" +
			"				foreach (transaction[i]) {\n" +
			"					if (i <length) {\n" +
			"						transaction[i].byte_en == get_byte_en(.tran_num (i), \n" +
			"							.be       (data.byte_en), \n" +
			"							.cpu      (cfg.cpu));\n" +
			"					}\n" +
			"				}\n" +
			"			}\n" +
			"	}\n" +
			"endclass\n"
			;
		
		runTest(doc, new String[] {"top", "some_const"});
	}

	private void runTest(
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(getName());
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> result = SVDBTestUtils.parse(
				log, SVLanguageLevel.SystemVerilog, null, 
				new StringInputStream(doc), getName(), markers);
		
		SVDBFile file = result.second();
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		LogFactory.removeLogHandle(log);
	}
	
}

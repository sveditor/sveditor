package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseClassDecl extends TestCase {
	
	public void testParseGlobalInterfaceClassDeclaration() throws SVParseException {
		String content = 
				"interface class foobar;\n" +
				"endclass\n"
				;
		
		runTest(content, new String[] {"foobar"});
	}
	
	public void testParsePackageInterfaceClassDeclaration() throws SVParseException {
		String content = 
				"package my_pkg;\n" +
				"	interface class foobar;\n" +
				"	endclass\n" +
				"endpackage\n"
				;
		
		runTest(content, new String[] {"my_pkg", "foobar"});
	}

	public void testParseModuleInterfaceClassDeclaration() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"module top;\n" +
				"	interface class foobar;\n" +
				"	endclass\n" +
				"endmodule\n"
				;
		
		runTest(content, new String[] {"top", "foobar"});
	}
	
	private void runTest(
			String			doc,
			String			exp_items[]) {
		runTest(null, getName(), doc, exp_items);
	}

	private void runTest(
			SVParserConfig	config,
			String			testname,
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(testname);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> result = SVDBTestUtils.parse(
				log, SVLanguageLevel.SystemVerilog, config, 
				new StringInputStream(doc), testname, markers);
		
		SVDBFile file = result.second();
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		LogFactory.removeLogHandle(log);
	}
}

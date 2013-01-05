package net.sf.sveditor.core.tests.argfile.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileStmt;
import net.sf.sveditor.core.parser.SVParseException;
import junit.framework.TestCase;

public class TestArgFileParserCornerCases extends TestCase {

	public void testMissingArgFileIncPath() throws SVParseException {
		String testname = "testArgFileInc";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"-f /tools/argfiles/argfile1.f\n" +
				"-file /tools/argfiles/argfile2.f\n" +
				"";
		
		ArgFileParserTests.runParserTest(testname, content, 
				new SVDBMarker[] {
				},
				new SVDBArgFileStmt[] {
					new SVDBArgFileIncFileStmt("/tools/argfiles/argfile1.f"),
					new SVDBArgFileIncFileStmt("/tools/argfiles/argfile2.f")
				});		
	}
}

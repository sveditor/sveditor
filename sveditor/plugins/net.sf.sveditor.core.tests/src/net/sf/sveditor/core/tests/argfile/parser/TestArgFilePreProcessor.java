package net.sf.sveditor.core.tests.argfile.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileVariableProviderList;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.parser.SVParseException;
import junit.framework.TestCase;

public class TestArgFilePreProcessor extends TestCase {
	
	public void testBraceDelimitedVarExpansion() throws SVParseException {
		ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(null);
		String testname = "testBraceDelimitedVarExpansion";
		String content =
				"+define+${VARIABLE1}=${VARIABLE2}\n"
				;
		
		SVCorePlugin.setenv("VARIABLE1", "value1");
		SVCorePlugin.setenv("VARIABLE2", "value2");
	
		ArgFileParserTests.runParserTest(vp, testname, content, 
				new SVDBArgFileDefineStmt("value1", "value2"));
	}
	
	public void testNonBraceDelimitedVarExpansion() throws SVParseException {
		ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(null);
		String testname = "testNonBraceDelimitedVarExpansion";
		String content =
				"+define+$VARIABLE1=$VARIABLE2\n"
				;
		
		SVCorePlugin.setenv("VARIABLE1", "value1");
		SVCorePlugin.setenv("VARIABLE2", "value2");
	
		ArgFileParserTests.runParserTest(vp, testname, content, 
				new SVDBArgFileDefineStmt("value1", "value2"));
	}
	
	public void testNonBraceDelimitedVarExpansion2() throws SVParseException {
		ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(null);
		String testname = "testNonBraceDelimitedVarExpansion2";
		String content =
				"/tools/$VARIABLE1/$VARIABLE2\n"
				;
		
		SVCorePlugin.setenv("VARIABLE1", "value1");
		SVCorePlugin.setenv("VARIABLE2", "value2");
	
		ArgFileParserTests.runParserTest(vp, testname, content, 
				new SVDBArgFilePathStmt("/tools/value1/value2"));
	}

}

package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;
import junit.framework.TestCase;

public class TestParseAssertions extends TestCase {
	
	public void testOvmXbusAssertions() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/xbus_assertions.sv",
				new String[] {"xbus_if"});
	}

	public void testOvmXbusAssertions_repetition() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/xbus_assertions.sv",
				new String[] {"xbus_if"});
	}

	public void testBasicProperties() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/basic_properties.sv",
				new String[] {"my_module"});
	}

}

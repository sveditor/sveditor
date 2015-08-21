package net.sf.sveditor.core.tests.parser.db;

import junit.framework.TestSuite;

public class ParserDBTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ParserDBTests");
		
		s.addTest(new TestSuite(TestParseModuleDB.class));
		
		return s;
	}

}

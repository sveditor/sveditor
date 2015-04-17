package net.sf.sveditor.core.tests.db;

import junit.framework.TestSuite;

public class SVDBTests extends TestSuite {
	
	public SVDBTests() {
		addTest(new TestSuite(TestSVDBLocation.class));
	}
	
	public static TestSuite suite() {
		return new SVDBTests();
	}

}

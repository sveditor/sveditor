package net.sf.sveditor.core.tests.searchutils;

import junit.framework.TestSuite;

public class SearchUtilsTests {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite();
		
		s.addTest(new TestSuite(TestFindItem.class));
		
		return s;
	}

}

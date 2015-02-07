package net.sf.sveditor.core.tests.search;

import junit.framework.TestSuite;

public class SearchTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("SearchTests");
		s.addTest(new TestSuite(TestSearchEngineFindDecl.class));
		
		return s;
	}

}

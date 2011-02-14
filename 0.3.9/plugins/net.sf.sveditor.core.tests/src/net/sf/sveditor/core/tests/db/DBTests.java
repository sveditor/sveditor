package net.sf.sveditor.core.tests.db;

import junit.framework.TestSuite;

public class DBTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite suite = new TestSuite();
		suite.addTest(new TestSuite(TestMerge.class));
		suite.addTest(new TestSuite(TestInitDuplicate.class));
		return suite;
	}

}

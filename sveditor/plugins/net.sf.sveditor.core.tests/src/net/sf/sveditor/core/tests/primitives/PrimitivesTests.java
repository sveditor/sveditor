package net.sf.sveditor.core.tests.primitives;

import junit.framework.TestSuite;

public class PrimitivesTests extends TestSuite {
	
	
	public static TestSuite suite() {
		TestSuite suite = new TestSuite();
		suite.addTest(new TestSuite(TestStringTextScanner.class));
		
		return suite;
	}

}

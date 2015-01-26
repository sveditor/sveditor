package net.sf.sveditor.core.tests.logscanner;

import junit.framework.TestSuite;

public class LogScannerTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite ret = new TestSuite();
		
		ret.addTest(new TestSuite(TestQuestaLogScanner.class));
		ret.addTest(new TestSuite(TestVerilatorLogScanner.class));
		ret.addTest(new TestSuite(TestMakefileLogScanner.class));
		
		return ret;
	}

}

package net.sf.sveditor.core.tests.index.argfile2;

import junit.framework.TestSuite;

public class ArgFileIndex2Tests extends TestSuite {
	
	public ArgFileIndex2Tests() {
		addTest(new TestSuite(TestSrcFileChange.class));
		addTest(new TestSuite(TestArgFileChange.class));
		addTest(new TestSuite(TestGetFilePath.class));
		addTest(new TestSuite(TestSVDBIndexUtil.class));
	}
	
	public static TestSuite suite() {
		return new ArgFileIndex2Tests();
	}

}

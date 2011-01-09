package net.sf.sveditor.core.tests.open_decl;

import junit.framework.TestSuite;

public class OpenDeclTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("OpenDeclTests");
		s.addTest(new TestSuite(TestOpenFile.class));
		s.addTest(new TestSuite(TestOpenClass.class));
		
		return s;
	}
	

}

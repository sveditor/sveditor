package net.sf.sveditor.core.tests.argfile.open_decl;

import junit.framework.TestSuite;

public class ArgFileOpenDeclTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite suite = new TestSuite("ArgFileOpenDeclTests");
		
		suite.addTest(new TestSuite(TestArgFileOpenPathDecl.class));
		
		return suite;
	}

}

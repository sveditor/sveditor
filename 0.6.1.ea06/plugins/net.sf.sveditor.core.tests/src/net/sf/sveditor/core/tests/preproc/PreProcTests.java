package net.sf.sveditor.core.tests.preproc;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class PreProcTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("PreProcTests");
		suite.addTest(new TestSuite(TestPreProc.class));
		return suite;
	}

}

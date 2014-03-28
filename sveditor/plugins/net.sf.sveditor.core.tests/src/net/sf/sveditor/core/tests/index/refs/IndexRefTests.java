package net.sf.sveditor.core.tests.index.refs;

import junit.framework.Test;
import junit.framework.TestSuite;

public class IndexRefTests extends TestSuite {

	public static Test suite() {
		TestSuite suite = new TestSuite("IndexRefTests");
		
		suite.addTest(new TestSuite(TestInstanceTreeFactory.class));
		suite.addTest(new TestSuite(TestClassRefs.class));
		
		return suite;
	}
}

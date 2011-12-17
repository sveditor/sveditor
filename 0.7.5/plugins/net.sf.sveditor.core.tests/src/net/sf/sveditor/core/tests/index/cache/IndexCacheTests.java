package net.sf.sveditor.core.tests.index.cache;

import junit.framework.Test;
import junit.framework.TestSuite;

public class IndexCacheTests extends TestSuite {

	public static Test suite() {
		TestSuite suite = new TestSuite("IndexTests");
		suite.addTest(new TestSuite(TestIndexCache.class));
		
		return suite;
	}

}

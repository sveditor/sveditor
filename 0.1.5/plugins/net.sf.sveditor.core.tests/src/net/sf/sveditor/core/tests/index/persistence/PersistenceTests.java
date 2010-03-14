package net.sf.sveditor.core.tests.index.persistence;

import junit.framework.Test;
import junit.framework.TestSuite;

public class PersistenceTests {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("PersistenceTests");
		suite.addTest(new TestSuite(TestFilesystemLibPersistence.class));
		suite.addTest(new TestSuite(TestWorkspaceLibPersistence.class));
		suite.addTest(new TestSuite(ArgFilePersistence.class));
		
		return suite;
	}

}

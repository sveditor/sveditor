package net.sf.sveditor.core.tests;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.tests.content_assist.ContentAssistBasics;
import net.sf.sveditor.core.tests.indent.IndentTests;
import net.sf.sveditor.core.tests.indent.NoHangIndentTests;
import net.sf.sveditor.core.tests.index.persistence.TestFilesystemLibPersistence;
import net.sf.sveditor.core.tests.index.persistence.TestWorkspaceLibPersistence;

public class ReleaseTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite();
		suite.addTest(new TestSuite(SVScannerTests.class));
		suite.addTest(new TestSuite(NoHangIndentTests.class));
		suite.addTest(new TestSuite(IndentTests.class));
		suite.addTest(new TestSuite(ContentAssistBasics.class));
		suite.addTest(new TestSuite(TestFilesystemLibPersistence.class));
		suite.addTest(new TestSuite(TestWorkspaceLibPersistence.class));
		
		return suite;
	}
	
}

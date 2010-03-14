package net.sf.sveditor.core.tests.content_assist;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class ContentAssistTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("ContentAssistTests");
		suite.addTest(new TestSuite(ContentAssistBasics.class));
		
		return suite;
	}

}

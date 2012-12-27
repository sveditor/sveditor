package net.sf.sveditor.core.tests.templates.sim;

import junit.framework.TestSuite;

public class TemplateSimTests extends TestSuite {

	public static TestSuite suite() {
		TestSuite suite = new TestSuite();
		
		if (System.getenv("SVE_QUESTA_EN") != null &&
				System.getenv("SVE_QUESTA_EN").equals("1")) {
			suite.addTest(new TestSuite(TestUVMTemplates.class));
		}
		
		return suite;
	}

}

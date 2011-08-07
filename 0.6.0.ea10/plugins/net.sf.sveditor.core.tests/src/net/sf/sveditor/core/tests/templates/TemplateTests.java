package net.sf.sveditor.core.tests.templates;

import junit.framework.TestSuite;

public class TemplateTests extends TestSuite {

	public static TestSuite suite() {
		TestSuite s = new TestSuite();
		s.addTest(new TestSuite(TestMethodologyTemplates.class));
		return s;
	}
}

package net.sf.sveditor.ui.tests.console;

import junit.framework.TestSuite;

public class ConsoleTests extends TestSuite {
	
	public ConsoleTests() {
		addTest(new TestSuite(TestPathPatternMatcher.class));
	}

	public static TestSuite suite() {
		return new ConsoleTests();
	}
}

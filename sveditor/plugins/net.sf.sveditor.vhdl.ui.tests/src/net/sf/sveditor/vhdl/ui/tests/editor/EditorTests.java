package net.sf.sveditor.vhdl.ui.tests.editor;

import junit.framework.TestCase;
import junit.framework.TestSuite;

public class EditorTests extends TestCase {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite();
		s.addTest(new TestSuite(TestBlockComment.class));
		
		return s;
	}

}

package net.sf.sveditor.vhdl.ui.tests;

import junit.framework.Test;
import junit.framework.TestSuite;
import net.sf.sveditor.ui.tests.utils.editor.AutoEditTester;
import net.sf.sveditor.vhdl.ui.editor.VHDLDocumentPartitions;
import net.sf.sveditor.vhdl.ui.tests.editor.EditorTests;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;

public class VhdlUiReleaseTests {
	
	public static Test suite() {
		TestSuite s = new TestSuite();
		
		s.addTest(EditorTests.suite());
		
		return s;
	}
	
	public static AutoEditTester createAutoEditTester() {
		IDocument doc = new Document();
		AutoEditTester tester = new AutoEditTester(doc, VHDLDocumentPartitions.VHD_PARTITIONING);
	
//		tester.setAutoEditStrategy(IDocument.DEFAULT_CONTENT_TYPE, aes);

		return tester;
	}
}

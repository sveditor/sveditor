package net.sf.sveditor.core.tests.argfile.open_decl;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.argfile.parser.SVArgFileExprContext;
import net.sf.sveditor.core.argfile.parser.SVArgFileExprScanner;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;

public class TestArgFileOpenPathDecl extends TestCase {
	
	public void testArgFileScanner_FilePath() {
		String testname = "testArgFileScanner_FilePath";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc =
			"+incdir+../../foo\n" +
			"${VARIABLE}/foo/bar\n" + // << Mark is here
			"\n"
			;
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("foo/bar");
		log.debug("index: " + idx);
		scanner.seek(idx+"foo".length()+1);
		
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, true);
	
		assertEquals("${VARIABLE}/foo/bar", ctxt.fLeaf);
	}

	public void testArgFileScanner_IncDirPath() {
		String testname = "testArgFileScanner_IncDirPath";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc =
			"+incdir+../../foo\n" + // << Mark is here
			"${VARIABLE}/foo/bar\n" + 
			"\n"
			;
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("../foo");
		log.debug("index: " + idx);
		scanner.seek(idx);
		
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, true);
	
		assertEquals("../../foo", ctxt.fLeaf);
		assertEquals("+incdir+", ctxt.fRoot);
	}

	
	public void testArgFileScanner_IncPath() {
		String testname = "testArgFileScanner_IncPath";
		SVCorePlugin.getDefault().enableDebug(true);
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc =
			"-INC ../../foo\n" + // << Mark is here
			"${VARIABLE}/foo/bar\n" + 
			"\n"
			;
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("../foo");
		log.debug("index: " + idx);
		scanner.seek(idx);
		
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, true);
	
		assertEquals("../../foo", ctxt.fLeaf);
		assertEquals("-INC", ctxt.fRoot);
	}	

	public void testArgFileScanner_PathAfterIncPath() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(true);
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc =
			"+incdir+${DIR}/files/incpath\n" +
			"${DIR}/files/file1.sv\n" +
			"${DIR}/files/file2.sv\n" +
			"\n"
			;
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("${DIR}/files/file1.sv");
		log.debug("index: " + idx);
		scanner.seek(idx+"${DIR}/files/fil".length());
		
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, true);
		
		log.debug("ctxt.fLeaf=" + ctxt.fLeaf);
		log.debug("ctxt.fRoot=" + ctxt.fRoot);
	
		assertEquals(null, ctxt.fRoot);
		assertEquals("${DIR}/files/file1.sv", ctxt.fLeaf);
	}
	
}

package net.sf.sveditor.core.tests.logscanner;

import net.sf.sveditor.core.script.launch.GccLogMessageScanner;
import net.sf.sveditor.core.script.launch.LogMessageScannerMgr;
import net.sf.sveditor.core.script.launch.MakefileLogMessageScanner;
import net.sf.sveditor.core.script.launch.ScriptMessage;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestGccLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new GccLogMessageScanner());
	}
	
	public void testBasics() {
		fScannerMgr.line("/home/test/foo/test.cpp:1:10: error: compilation error");
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.cpp", m.getPath());
		assertEquals(1, m.getLineno());
	}
}

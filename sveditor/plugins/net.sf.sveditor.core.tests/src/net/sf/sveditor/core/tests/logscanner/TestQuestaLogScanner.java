package net.sf.sveditor.core.tests.logscanner;

import net.sf.sveditor.core.script.launch.LogMessageScannerMgr;
import net.sf.sveditor.core.script.launch.QuestaLogMessageScanner;
import net.sf.sveditor.core.script.launch.ScriptMessage;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestQuestaLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new QuestaLogMessageScanner());
	}
	
	public void testBasicError() {
		fScannerMgr.line("** Error: /home/test/foo/test.sv(1): compilation error");
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.sv", m.getPath());
		assertEquals(1, m.getLineno());
	}
	
	public void testErrorWithCode() {
		fScannerMgr.line("** Error: (vlog-1000) /home/test/foo/test.sv(1): compilation error");
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.sv", m.getPath());
		assertEquals(1, m.getLineno());
	}

	public void testSuppressibleError() {
		fScannerMgr.line("** Error (suppressible): (vlog-1100) /home/test/foo/test.sv(1): compilation error");
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.sv", m.getPath());
		assertEquals(1, m.getLineno());
	}

}

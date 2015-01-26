package net.sf.sveditor.core.tests.logscanner;

import net.sf.sveditor.core.script.launch.LogMessageScannerMgr;
import net.sf.sveditor.core.script.launch.ScriptMessage;
import net.sf.sveditor.core.script.launch.ScriptMessage.MessageType;
import net.sf.sveditor.core.script.launch.VerilatorLogMessageScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestVerilatorLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new VerilatorLogMessageScanner());
	}
	
	public void testBasicWarningMessage() {
		fScannerMgr.line("%Warning-WIDTH: /home/test/foo/test.sv:1: width is wrong");
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("width is wrong", m.getMessage());
		assertEquals("/home/test/foo/test.sv", m.getPath());
		assertEquals(1, m.getLineno());	
		assertEquals(MessageType.Warning, m.getType());
	}

}

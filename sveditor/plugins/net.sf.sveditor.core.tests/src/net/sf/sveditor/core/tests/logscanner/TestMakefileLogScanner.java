package net.sf.sveditor.core.tests.logscanner;

import net.sf.sveditor.core.script.launch.LogMessageScannerMgr;
import net.sf.sveditor.core.script.launch.MakefileLogMessageScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestMakefileLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new MakefileLogMessageScanner());
	}
	
	public void testBasicDirectoryChange() {
		fScannerMgr.line("make: Entering directory '/scratch/other/foo'");
		
		assertEquals("/scratch/other/foo", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
	}
	
	public void testBasicDirectoryChange2() {
		fScannerMgr.line("make[1]: Entering directory '/scratch/other/foo'");
		
		assertEquals("/scratch/other/foo", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make[1]: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make[1]: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
	}	
}

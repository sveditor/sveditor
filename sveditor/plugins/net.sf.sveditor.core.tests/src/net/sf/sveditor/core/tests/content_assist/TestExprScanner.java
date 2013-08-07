package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestExprScanner extends SVCoreTestCaseBase {
	
	public void testIncludeFindsQuotes() {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
				"`include \"\n"
				;

		StringBIDITextScanner ss = new StringBIDITextScanner(doc);
		ss.seek(doc.length()-1);
		
		SVExprScanner scanner = new SVExprScanner();
		SVExprContext ctxt = scanner.extractExprContext(ss, false);
		
		System.out.println("ctxt: " + ctxt.fRoot + " " + ctxt.fLeaf + " ");
	}

}

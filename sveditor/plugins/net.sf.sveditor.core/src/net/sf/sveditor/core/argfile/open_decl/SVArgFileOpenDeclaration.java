package net.sf.sveditor.core.argfile.open_decl;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.argfile.content_assist.SVArgFileExprContext;
import net.sf.sveditor.core.argfile.content_assist.SVArgFileExprScanner;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class SVArgFileOpenDeclaration {

	public static List<String> openDecl(IBIDITextScanner scanner) {
		LogHandle log = LogFactory.getLogHandle("SVargFileOpenDeclaration");
		
		List<String> ret = new ArrayList<String>();
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, true);
		
		log.debug("ctxt: " + ctxt.fRoot + " " + ctxt.fLeaf);
		
		return ret;
	}
	
}

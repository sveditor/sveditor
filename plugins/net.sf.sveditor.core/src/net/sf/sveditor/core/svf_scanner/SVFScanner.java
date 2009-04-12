package net.sf.sveditor.core.svf_scanner;

import net.sf.sveditor.core.scanutils.ITextScanner;

/**
 * SVFScanner provides a scanner for the .f files that are often used to
 * specify command-line arguments to a verilog compiler.
 * 
 * @author ballance
 *
 */
public class SVFScanner {
	private ITextScanner				fScanner;
	
	public SVFScanner(ITextScanner scanner) {
		fScanner = scanner;
	}
	
	public void scan() {
		
	}

}

package net.sf.sveditor.core.preproc;

import java.io.InputStream;

import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcessor extends AbstractTextScanner {
	private IPreProcMacroProvider		fMacroProvider;
	private boolean					fInString;
	private InputStreamTextScanner		fScanner;
	private StringBuilder				fContent;
	private int						fIdx;

	private static final int    PP_DISABLED 			= 0;
	private static final int    PP_ENABLED  			= 1;
	
	// This bit is set when we are within a disabled section.
	// It's impossible for anything in a sub-section to be enabled
	private static final int    PP_CARRY    			= 2;
	
	// This bit is set when a block within this level of conditionals
	// has been taken (ie `ifdef (true) ... ; `ifndef (false))
	private static final int	PP_THIS_LEVEL_EN_BLOCK 	= 4;
	
	public SVPreProcessor(InputStream in, IPreProcMacroProvider macro_provider) {
		fContent = new StringBuilder();
		fScanner = new InputStreamTextScanner(in, "");
		fMacroProvider = macro_provider;
	}
	
	@Override
	public void init() {
		super.init();
		preprocess();
	}

	private void preprocess() {
		int ch;
		
		while ((ch = fScanner.get_ch()) != -1) {
			if (ch == '/' && !fInString) {
				int ch2 = fScanner.get_ch();
				
				if (ch2 == '/') {
					fContent.append((char)0);
					fContent.append("//");
					while ((ch = fScanner.get_ch()) != -1 && ch != '\n') { }
				} else if (ch2 == '*') {
				} else {
					
				}
			}
			
		}
	}

	public int get_ch() {
		if (fIdx < fContent.length()) {
			return fContent.charAt(fIdx++);
		} else {
			return -1;
		}
	}

	public void unget_ch(int ch) {
		if (fIdx > 0) {
			fIdx--;
		}
	}

	public ScanLocation getLocation() {
		return new ScanLocation("", fLineno, fLinepos);
	}

	public long getPos() {
		return fIdx;
	}
	
}

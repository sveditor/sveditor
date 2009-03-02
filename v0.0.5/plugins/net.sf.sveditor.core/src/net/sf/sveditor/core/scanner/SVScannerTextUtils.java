package net.sf.sveditor.core.scanner;

public class SVScannerTextUtils extends AbstractTextScanner {
	private SVPreProcScanner			fScanner;
	private StringBuffer				fUngetStr;
	
	public SVScannerTextUtils(SVPreProcScanner scanner) {
		super();
		fScanner        = scanner;
		fUngetStr       = new StringBuffer();
	}
	
	public int get_ch() {
		return get_ch(false);
	}
	
	private int get_ch(boolean throw_ex) {
		int ch = -1;
		
		if (fUngetStr.length() > 0) {
			ch = fUngetStr.charAt(fUngetStr.length()-1);
			fUngetStr.setLength(fUngetStr.length()-1);
		} else {
			ch = fScanner.get_ch();
		}

		if (ch != -1 && fCaptureEnabled) {
			fCaptureBuffer.append((char)ch);
		}
		
		return ch;
	}
	
	public void unget_ch(int ch) {
		fUngetStr.append((char)ch);
	}
	

	public int skipPastMatch(String pair, String escape) throws EOFException {
		int begin = pair.charAt(0);
		int end = pair.charAt(1);
		int matchLevel = 1;
		int ch;
		
		do {
			ch = get_ch();
			if (ch == begin) {
				matchLevel++;
			} else if (ch == end) {
				matchLevel--;
			} else {
				boolean do_escape = false;
				for (int i=0; i<escape.length(); i++) {
					if (ch == escape.charAt(i)) {
						do_escape = true;
						break;
					}
				}
				if (do_escape) {
					unget_ch(ch);
					break;
				}
			}
		} while (matchLevel > 0 && ch != -1);
		
		return get_ch();
	}
	
	/*
	public String readExpression(int ch) {
		fTmpBuffer.setLength(0);
		
	}
	 */
	
	public void unget_str(String str) {
		for (int i=str.length()-1; i>=0; i--) {
			fUngetStr.append(str.charAt(i));
		}
	}
	
	public ScanLocation getLocation() {
		return fScanner.getLocation();
	}
}

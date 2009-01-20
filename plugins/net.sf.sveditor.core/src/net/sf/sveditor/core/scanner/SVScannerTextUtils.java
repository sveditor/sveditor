package net.sf.sveditor.core.scanner;

public class SVScannerTextUtils {
	private SVPreProcScanner			fScanner;
	private StringBuffer				fTmpBuffer;
	private StringBuffer				fCaptureBuffer;
	private boolean						fCaptureEnabled;
	private StringBuffer				fUngetStr;
	
	public SVScannerTextUtils(SVPreProcScanner scanner) {
		fScanner        = scanner;
		fTmpBuffer      = new StringBuffer();
		fCaptureBuffer  = new StringBuffer();
		fUngetStr       = new StringBuffer();
		fCaptureEnabled = false;
	}
	
	public int get_ch() throws EOFException {
		return get_ch(false);
	}
	
	public int get_ch(boolean throw_ex) throws EOFException {
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
	
	public int skipWhite(int ch) throws EOFException {
		
		while (Character.isWhitespace(ch) || ch == '\\') {
			int tmp = get_ch();
			
			if (ch == '\\' && (tmp != '\r' && tmp != '\n')) {
				unget_ch(tmp);
				return ch;
			}
			ch = tmp;
		}
		return ch;
	}
	
	public String readIdentifier(int ci) throws EOFException {
		fTmpBuffer.setLength(0);
		
		try {
			if (!Character.isJavaIdentifierStart(ci)) {
				unget_ch(ci);
				return null;
			}
		
			fTmpBuffer.append((char)ci);
		
			while ((ci = get_ch()) != -1 && 
					(Character.isJavaIdentifierPart(ci) || ci == ':')) {
				fTmpBuffer.append((char)ci);
			}
			unget_ch(ci);
			
			// Even though ':' can appear as part of the identifier, it
			// must not appear at the end of an identifier
			while (fTmpBuffer.length() > 0 && 
					fTmpBuffer.charAt(fTmpBuffer.length()-1) == ':') {
				unget_ch(':');
				fTmpBuffer.setLength(fTmpBuffer.length()-1);
			}
		} catch (EOFException e) {
			if (fTmpBuffer.length() == 0) {
				throw e;
			}
		}
		
		return fTmpBuffer.toString();
	}
	
	public void startCapture(int ch) {
		fCaptureEnabled = true;
		fCaptureBuffer.setLength(0);
		if (ch != -1) {
			fCaptureBuffer.append((char)ch);
		}
	}
	
	public String endCapture() {
		fCaptureEnabled = false;
		return fCaptureBuffer.toString();
	}
	
	public int skipPastMatch(String pair) throws EOFException {
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
			}
		} while (matchLevel > 0 && ch != -1);
		
		return get_ch();
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
	
	public void unget_str(String str) {
		for (int i=str.length()-1; i>=0; i--) {
			fUngetStr.append(str.charAt(i));
		}
	}
	
	public ScanLocation getLocation() {
		return fScanner.getLocation();
	}
}

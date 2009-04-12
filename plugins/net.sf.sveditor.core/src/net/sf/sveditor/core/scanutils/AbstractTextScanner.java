package net.sf.sveditor.core.scanutils;


public abstract class AbstractTextScanner implements ITextScanner {
	protected StringBuilder				fTmpBuffer;
	protected StringBuilder				fCaptureBuffer;
	protected boolean					fCaptureEnabled;
	protected int						fLineno;
	protected int						fLastCh;

	public AbstractTextScanner() {
		fTmpBuffer      = new StringBuilder();
		fCaptureBuffer  = new StringBuilder();
		fCaptureEnabled = false;
		fLastCh  = -1;
		fLineno  = 1;
	}
	
	public void init() {
		fCaptureEnabled = false;
	}
	
	public int skipWhite(int ch) {
		
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

	public String readIdentifier(int ci) {
		fTmpBuffer.setLength(0);
		
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
		
		return (fTmpBuffer.length()>0)?fTmpBuffer.toString():null;
	}
	
	public String readString(int ch) {
		fTmpBuffer.setLength(0);
		int last_ch = -1;
		
		if (ch != '"') {
			return null;
		}
		
		ch = get_ch();
		while (((ch != '"' && ch != '\n') || last_ch == '\\') && ch != -1) {
			if (last_ch == '\\' && ch == '"') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, '"');
				}
			} else if (last_ch == '\\' && ch == '\n') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\r') {
					fTmpBuffer.setLength(fTmpBuffer.length()-1);
				}
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, ' ');
				}
			} else {
				fTmpBuffer.append((char)ch);
			}
			
			if (ch != '\r') {
				last_ch = ch;
			}
			
			ch = get_ch();
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

	public int skipPastMatch(String pair) {
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

}

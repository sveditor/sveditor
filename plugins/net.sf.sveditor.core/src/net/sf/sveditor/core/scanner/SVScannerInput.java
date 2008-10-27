package net.sf.sveditor.core.scanner;

import java.io.IOException;
import java.io.InputStream;

public class SVScannerInput {
	private String				fName;
	private InputStream			fInput;
	
	private StringBuffer		fUngetStr;
	private int					fPos;
	private int					fLineno;
	private int					fLinepos;
	private int					fLastch;
	
	private StringBuffer		fCaptureBuffer = new StringBuffer();
	private boolean				fCaptureEnabled = false;
	private StringBuffer		fUnaccContent = new StringBuffer();
	
	
	public SVScannerInput(String name, InputStream in) {
		fUngetStr = new StringBuffer();
		fName = name;
		fInput = in;
	}
	
	public ScanLocation getLocation() {
		return new ScanLocation(fName, fLineno, fLinepos);
	}
	
	public String getName() {
		return fName;
	}
	
	public int get_ch() throws EOFException {
		int ch;
		
		if (fUnaccContent.length() > 0) {
			ch = fUnaccContent.charAt(fUnaccContent.length()-1);
			fUnaccContent.setLength(fUnaccContent.length()-1);
			
			// unaccounted 
			return ch;
		} else if (fUngetStr.length() > 0) {
			ch = fUngetStr.charAt(fUngetStr.length()-1);
			fUngetStr.setLength(fUngetStr.length()-1);
		} else {
			try {
				ch = fInput.read(); 
			} catch (IOException e) {
				ch = -1;
			}
		}
		
		if (ch != -1) {
			if (fLastch == '\n') {
				fLineno++;
				fLinepos = 0;
			}
			fPos++;
			fLinepos++;
			fLastch = ch;
		} else {
			throw new EOFException();
		}
	
		return ch;
	}
	
	public void unget_ch(int ch) {
		if (fUnaccContent.length() > 0) {
			fUnaccContent.append((char)ch);
		} else {
			fUngetStr.append((char)ch);
			
			if (ch == '\n') {
				fLineno--;
			}
		}
	}
	
	public void unget_str(String str) {
		if (fUnaccContent.length() > 0) {
			for (int i=str.length()-1; i>=0; i--) {
				fUnaccContent.append(str.charAt(i));
			}
		} else {
			for (int i=str.length()-1; i>=0; i--) {
				fUngetStr.append(str.charAt(i));
				if (str.charAt(i) == '\n') {
					fLineno--;
				}
			}
		}
	}
	
	public void pushUnaccContent(String str) {
		for (int i=str.length()-1; i>=0; i--) {
			fUnaccContent.append((char)str.charAt(i));
		}
	}
	
	public void startCapture(int ch) {
		fCaptureEnabled = true;
		fCaptureBuffer.setLength(0);
		if (ch != -1) {
			fCaptureBuffer.append((char)ch);
		}
	}
	
	public String endCapture() throws EOFException {
		fCaptureEnabled = false;
		return fCaptureBuffer.toString();
	}
	
	public int skipWhite(int ch) throws EOFException {

		// Skip whitespace. Consider the line-continuation character as WS
		while (Character.isWhitespace(ch) || ch == '\\') {
			int tmp = next_ch();
			
			if (ch == '\\' && (tmp != '\r' && tmp != '\n')) {
				unget_ch(tmp);
				return ch;
			}
			ch = tmp;
		}
		
		return ch;
	}
	
	public int skipPastMatch(String pair) throws EOFException {
		int begin = pair.charAt(0);
		int end = pair.charAt(1);
		int matchLevel = 1;
		int ch;
		
		do {
			ch = next_ch();
			if (ch == begin) {
				matchLevel++;
			} else if (ch == end) {
				matchLevel--;
			}
		} while (matchLevel > 0 && ch != -1);
		
		return next_ch();
	}

	public int skipPastMatch(String pair, String escape) throws EOFException {
		int begin = pair.charAt(0);
		int end = pair.charAt(1);
		int matchLevel = 1;
		int ch;
		
		do {
			ch = next_ch();
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
		
		return next_ch();
	}

	public int next_ch() throws EOFException {
		int ch;
		
		ch = get_ch();
		
		if (ch == '/') {
			int ch2 = get_ch();
			
			if (ch2 == '/') {
				// skip to EOL
				// save beginning of comment
				fCaptureBuffer.setLength(0);
				fCaptureBuffer.append("//");
				while ((ch = get_ch()) != -1  && ch != '\n') {
					fCaptureBuffer.append((char)ch);
				}
				
				// TODO: pass comment to observer

				return ' ';
			} else if (ch2 == '*') {
				int end_comment[] = {-1, -1};
				
				fCaptureBuffer.setLength(0);
				fCaptureBuffer.append("/*");
				while ((ch = get_ch()) != -1) {
					end_comment[0] = end_comment[1];
					end_comment[1] = ch;
					
					
					fCaptureBuffer.append((char)ch);
					
					if (end_comment[0] == '*' && end_comment[1] == '/') {
						break;
					}
				}
				
				return ' ';
			} else {
				// Just a literal '/'
				unget_ch(ch2);
				return ch;
			}
		} else if (ch == '"') {
			// string literal
			int ch_l = -1;

			fCaptureBuffer.setLength(0);
			while ((ch = get_ch()) != -1 &&
					ch != '"' && ch_l != '\\') {
				ch_l = ch;
				fCaptureBuffer.append((char)ch);
			}
			
			return ' ';
		} else {
			if (fCaptureEnabled) {
				fCaptureBuffer.append((char)ch);
			}
			return ch;
		}
	}
	
	public String readIdentifier(int ci) throws EOFException {
		StringBuffer buf = null;
		
		try {
			if (!Character.isJavaIdentifierStart(ci)) {
				unget_ch(ci);
				return null;
			}
		
			buf = new StringBuffer();
			buf.append((char)ci);
		
			while ((ci = get_ch()) != -1 && Character.isJavaIdentifierPart(ci)) {
				buf.append((char)ci);
			}
			unget_ch(ci);
		} catch (EOFException e) {
			if (buf.length() == 0) {
				throw e;
			}
		}
		
		return buf.toString();
	}
	
	public String readLine(int ci) throws EOFException {
		int last_ch = -1;
		StringBuffer ret = new StringBuffer();

		try {
			while (ci != '\n' || last_ch == '\\') {
				if (last_ch == '\\' && ci == '\n') {
					if (ret.charAt(ret.length()-1) == '\r') {
						ret.setLength(ret.length()-1);
					}
					if (ret.charAt(ret.length()-1) == '\\') {
						ret.setCharAt(ret.length()-1, '\n');
					}
				} else {
					ret.append((char)ci);
				}

				if (ci != '\r') {
					last_ch = ci;
				}

				ci = get_ch();
			}
		} catch (EOFException e) {
			if (ret.length() == 0) {
				throw e;
			}
		}
		
		return ret.toString();
	}
	
	public String readString(int ci) throws EOFException {
		StringBuffer ret = new StringBuffer();
		int last_ch = -1;
		
		if (ci != '"') {
			return null;
		}
		
		ci = get_ch();
		while ((ci != '"' && ci != '\n') || last_ch == '\\') {
			if (last_ch == '\\' && ci == '"') {
				if (ret.charAt(ret.length()-1) == '\\') {
					ret.setCharAt(ret.length()-1, '"');
				}
			} else if (last_ch == '\\' && ci == '\n') {
				if (ret.charAt(ret.length()-1) == '\r') {
					ret.setLength(ret.length()-1);
				}
				if (ret.charAt(ret.length()-1) == '\\') {
					ret.setCharAt(ret.length()-1, ' ');
				}
			} else {
				ret.append((char)ci);
			}
			
			if (ci != '\r') {
				last_ch = ci;
			}
			
			ci = get_ch();
		}
		
		return ret.toString();
	}
	
	public int skipToCharOR(int ch, String or_list) throws EOFException {

		while (ch != -1) {
			for (int i=0; i<or_list.length(); i++) {
				if (or_list.charAt(i) == ch) {
					break;
				}
			}
			
			ch = next_ch();
		}
		
		return ch;
	}

	public int skipToChar(int ch, int match_ch) throws EOFException {

		while (ch != -1) {
			if (ch == match_ch) {
				break;
			}
			
			ch = next_ch();
		}
		
		return ch;
	}

}

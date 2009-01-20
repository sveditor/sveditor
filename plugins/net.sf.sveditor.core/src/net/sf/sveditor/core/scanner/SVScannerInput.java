package net.sf.sveditor.core.scanner;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.StringInputStream;

public class SVScannerInput {
	private String				fName;
	private InputStream			fInput;
	private byte				fInputBuffer[] = new byte[65536];
	private int					fInputBufferIdx = 0;
	private int					fInputBufferMax = 0;
	
	private StringBuffer		fUngetStr;
	private int					fPos;
	private int					fLineno;
	private int					fLinepos;
	private int					fLastch;
	private int					fUngetCh = -1;
	
	private StringBuffer		fPPBuffer = new StringBuffer();
	
	private StringBuffer		fCaptureBuffer = new StringBuffer();
	private boolean				fCaptureEnabled = false;
	private StringBuffer		fCommentBuffer = new StringBuffer();
	private StringBuffer		fUnaccContent = new StringBuffer();
	private ISVScannerObserver	fObserver;
	private IDefineProvider		fDefineProvider;
	private Stack<Boolean>		fPreProcEn  = new Stack<Boolean>();
	private ISVScanner			fScanner;
	
	
	public SVScannerInput(
			String 				name, 
			InputStream 		in,
			ISVScanner			scanner,
			ISVScannerObserver	observer,
			IDefineProvider		define_provider) {
		fUngetStr = new StringBuffer();
		fName = name;
		fInput = in;
		fObserver       = observer;
		fDefineProvider = define_provider;
		fLineno         = 1;
		fScanner        = scanner;
		
		fPreProcEn.clear();
		fPreProcEn.push(true);
	}
	
	public ScanLocation getLocation() {
		return new ScanLocation(fName, fLineno, fLinepos);
	}
	
	public String getName() {
		return fName;
	}
	
	public int get_ch() throws EOFException {
		int ch;

		// Skip characters in disabled regions
		do {
			ch = get_ch_pp();
		} while (!fPreProcEn.peek() && ch != -1);
		
		if (ch == -1) {
			throw new EOFException();
		}
	
		return ch;
	}
	
	private int get_ch_pp() throws EOFException {
		int ch = -1, ch2;
		boolean cont = false;
		
		do {
			cont = false;
			if (fUnaccContent.length() > 0) {
				// Anything that is unaccounted is pure pass-through
				ch = fUnaccContent.charAt(fUnaccContent.length()-1);
				fUnaccContent.setLength(fUnaccContent.length()-1);
				
				// unaccounted 
				return ch;
			} else if (fUngetStr.length() > 0) {
				ch = fUngetStr.charAt(fUngetStr.length()-1);
				fUngetStr.setLength(fUngetStr.length()-1);
			} else {
				ch = get_ch_ll();
			}
			
			if (ch == '/') {
				ch2 = get_ch_ll();
				
				if (ch2 == '/') {
					// skip to EOL
					fCommentBuffer.setLength(0);
					fCommentBuffer.append("//");
					while ((ch = get_ch_ll()) != -1  && ch != '\n') {
						fCommentBuffer.append((char)ch);
					}

					if (fObserver != null) {
						fObserver.comment(fCommentBuffer.toString());
					}

					ch = '\n';
				} else if (ch2 == '*') {
					int end_comment[] = {-1, -1};
					
					fCommentBuffer.setLength(0);
					fCommentBuffer.append("/*");
					while ((ch = get_ch_ll()) != -1) {
						end_comment[0] = end_comment[1];
						end_comment[1] = ch;
						

						fCommentBuffer.append((char)ch);
						
						if (end_comment[0] == '*' && end_comment[1] == '/') {
							break;
						}
					}
					
					if (fObserver != null) {
						fObserver.comment(fCommentBuffer.toString());
					}
					
					ch = ' ';
				} else {
					// Just a literal '/'
					unget_ch(ch2);
				}
			} else if (ch == '`') {
				ch2 = get_ch_ll();
			
				// Only valid inside a definition
				/*
				if (ch2 == '`') {
					// just a literal `
				} else if (ch2 == '\\') {
					// could be a `\`
				} else if (ch2 == '"') {
					// escaped "
				} else {
				 */
				fPPBuffer.setLength(0);

				fPPBuffer.append((char)ch2);
				// read an identifier
				while ((ch2 = get_ch_ll()) != -1 && 
						Character.isJavaIdentifierPart(ch2)) {
					fPPBuffer.append((char)ch2);
				}

				if (ch2 != -1) {
					fUngetCh = ch2;
				}

				handle_preproc_directive(fPPBuffer.toString());
				cont = true;
			}
		} while (cont);
		
		return ch;
	}
	
	private int get_ch_ll() {
		int ch = -1;
		
		if (fUngetCh != -1) {
			ch = fUngetCh;
			fUngetCh = -1;
			return ch;
		}
		
		if (fInputBufferIdx >= fInputBufferMax) {
			// Try reading another//				System.out.println(fName + ": read " + fInputBufferMax + " chars");

			fInputBufferIdx = 0;
			try {
				fInputBufferMax = fInput.read(fInputBuffer, 0, fInputBuffer.length);
			} catch (IOException e) {
				fInputBufferMax = -1;
			}
		}
		
		if (fInputBufferIdx >= fInputBufferMax) {
			ch = -1;
		} else {
			ch = fInputBuffer[fInputBufferIdx++];
		}
		
		if (ch != -1) {
			if (fLastch == '\n') {
				fLineno++;
				fLinepos = 0;
			}
			fPos++;
			fLinepos++;
			fLastch = ch;
		}

		return ch;
	}
	
	public void unget_ch(int ch) {
		if (fUnaccContent.length() > 0) {
			fUnaccContent.append((char)ch);
		} else {
			fUngetStr.append((char)ch);
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
			}
		}
	}
	
	private void pushUnaccContent(String str) {
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
		
		
		if (ch == '"') {
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
		
			while ((ci = get_ch()) != -1 && 
					(Character.isJavaIdentifierPart(ci) || ci == ':')) {
				buf.append((char)ci);
			}
			unget_ch(ci);
			
			// Even though ':' can appear as part of the identifier, it
			// must not appear at the end of an identifier
			while (buf.length() > 0 && buf.charAt(buf.length()-1) == ':') {
				unget_ch(':');
				buf.setLength(buf.length()-1);
			}
		} catch (EOFException e) {
			if (buf == null || buf.length() == 0) {
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
	
	private void handle_preproc_directive(String type) throws EOFException {
		int ch = -1;
		
		if (type.equals("ifdef") || type.equals("ifndef")) {
			StringBuffer sb = new StringBuffer();
			int last_ch = -1;
			
			// TODO: use map
			ch = skipWhite(next_ch());
			
			while (true) {
				ch = next_ch();
				if (ch == '\n' && last_ch != '\\') {
					break;
				}
				if (ch != '\r') {
					last_ch = ch;
					sb.append((char)ch);
				}
				
				if (ch == '\n' && last_ch == '\\') {
					sb.setLength(sb.length()-2);
				}
			}
//FIXME:			fNewStatement = true;
			
			// TODO: need to actually evaluate the expression?
			if (type.equals("ifdef")) {
				fPreProcEn.push(false);
			} else {
				fPreProcEn.push(true);
			}
		} else if (type.equals("else")) {
			if (fPreProcEn.size() > 0) {
				boolean en = fPreProcEn.pop();
				fPreProcEn.push(!en);
			}
		} else if (type.equals("endif")) {
			if (fPreProcEn.size() > 0) {
				fPreProcEn.pop();
			}
		} else if (type.equals("timescale")) {
			// ignore
			// TODO: read to line-end
		} else if (type.equals("begin_keywords") || type.equals("end_keywords")) {
			// TODO: read to line-end 
		} else if (type.equals("define")) {
			List<String> params = new ArrayList<String>();

			// Push the line number up to the scanner
			if (fScanner != null) {
				fScanner.setStmtLocation(getLocation());
			}

			ch = skipWhite(get_ch_ll());
			StringBuffer def_line_i = new StringBuffer();
			def_line_i.append(readLine(ch));
			
			for (int i=0; i<def_line_i.length(); i++) {
				if (def_line_i.charAt(i) == '\n' && i+1 < def_line_i.length()) {
					def_line_i.insert(i, '\\');
					i++;
				}
			}
			
			String def_line = def_line_i.toString();
			
			
			SVScannerInput in = new SVScannerInput("define_processor",
					new StringInputStream(def_line), null,
					fObserver, fDefineProvider);
			
			String def_id = null;
			String define = "";
			
			try {
				int ch2 = in.skipWhite(in.get_ch());
				
				def_id = in.readIdentifier(ch2);

				// If this macro has parameters, the '(' is directly
				// after the end of the identifier -- no space
				ch2 = in.get_ch();
				
				if (ch2 == '(') {
					// macro parameters
					in.startCapture(-1);
					ch2 = in.skipPastMatch("()");
					String param_s = in.endCapture();
					param_s = param_s.substring(0, param_s.length()-2);
					ch2 = in.skipWhite(ch2);
					
					if (param_s != null && param_s.length() > 0) {
						for (String p : param_s.split(",")) {
							params.add(p.trim());
						}
					}
				}
				
				define = in.readLine(ch2);

			} catch (EOFException e) { }
			
			if (fObserver != null) {
				fObserver.preproc_define(def_id, params, define);
			}
		} else if (type.equals("include")) {
			ch = get_ch();
			
			while (Character.isWhitespace(ch)) {
				ch = get_ch();
			}

			if (ch == '"') {
				String inc = readString(ch);
				
				if (fObserver != null) {
					fObserver.preproc_include(inc);
				}
			}
		} else {
			List<String> params = new ArrayList<String>();
			// macro expansion
			
			if (fDefineProvider != null && fDefineProvider.hasParameters(type)) {
				
				/*
				System.out.println("processing expansion of macro \"" + type + 
						"\" @ "  + getLocation().getFileName() + ":" + 
						getLocation().getLineNo());
				 */

				ch = skipWhite(next_ch());
				
				// TODO: get params
				if (ch == '(') {
					startCapture(-1);
					ch = skipPastMatch("()");
					String body = endCapture();
					
					SVScannerInput in = new SVScannerInput(
							"p", new StringInputStream(body), 
							null, null, fDefineProvider);
					unget_ch(ch);
						
					do {
						String param = null;
						
						ch = in.next_ch();
						
						if (ch == '(') {
							// it's a paren-delimited token
							in.startCapture(ch);
							ch = in.skipPastMatch("()");
							param = in.endCapture();
						} else if (ch == '"') {
							// it's a string
							param = in.readString(ch);
							ch = in.get_ch();
						} else {
							StringBuffer p_b = new StringBuffer();
							// just read to the next ',' or ')'
							while (ch != -1 && ch != ',' && ch != ')') {
								p_b.append((char)ch);
								ch = in.next_ch();
							}
						
							if (p_b.length() > 0) {
								param = p_b.toString();
							}
						}
						
						if (param != null) {
							params.add(param);
						}
						
					} while (ch != -1 && ch != ')');
				} else {
					System.out.println("[ERROR] macro \"" +	type + "\" with parameters missing @ " + 
							getLocation().getFileName() + ":" + getLocation().getLineNo());
					/*
					System.out.println("    ch=\"" + (char)ch + "\"");
					 */
				}
			}
			
			String val = "";
			
			if (fDefineProvider != null) {
				val = fDefineProvider.getDefineVal(type, params);
			}
			
//			System.out.println("def value: \"" + val + "\"");

			if (val != null) {
				pushUnaccContent(val + "\n");
			}
			
//FIXME:			fNewStatement = true;
		}
	}
}

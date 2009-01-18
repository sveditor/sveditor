package net.sf.sveditor.core.scanner;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class SVPreProcScanner implements ISVScanner {
	private InputStream			fInput;
	private String				fFileName;
	
	private byte				fInputBuffer[] = new byte[1024 * 1024];
	private int					fInputBufferIdx = 0;
	private int					fInputBufferMax = 0;
	private int					fUngetCh = -1;
	private int					fLastCh  = -1;
	private int					fLineno;
	private StringBuffer		fPPBuffer;
	private StringBuffer		fTmpBuffer;
	private Stack<Boolean>		fPreProcEn;
	private List<String>		fParamList;
	private ISVScannerObserver	fObserver;
	private ScanLocation		fScanLocation;

	
	public SVPreProcScanner() {
		fPPBuffer  = new StringBuffer();
		fTmpBuffer = new StringBuffer();
		fPreProcEn = new Stack<Boolean>();
		fParamList = new ArrayList<String>();
		fScanLocation = new ScanLocation("", 0, 0);
	}
	
	public void setObserver(ISVScannerObserver observer) {
		fObserver = observer;
		fObserver.init(this);
	}
	
	@Override
	public ScanLocation getStmtLocation() {
		return fScanLocation;
	}

	@Override
	public void setStmtLocation(ScanLocation location) {
		// Do nothing
	}

	public void scan(InputStream in, String name) {
		int     ch;
		boolean new_stmt = true;
		
//		System.out.println("Scan file \"" + name + "\"");
		
		fLineno = 1;
		fScanLocation.setLineNo(1);
		
		fPPBuffer.setLength(0);
		fTmpBuffer.setLength(0);
		fPreProcEn.clear();
		
		fPreProcEn.push(true);
		
		fInput    = in;
		fFileName = name;
		
		fScanLocation.setFileName(name);
		

		if (fObserver != null) {
			fObserver.enter_file(fFileName);
		}
		
		while ((ch = get_ch()) != -1) {
			// Scan statements, while detecting pre-processor directives
			if (ch == ';' || ch == '\n') {
				new_stmt = true;
			} else if (!Character.isWhitespace(ch)) {
				if (new_stmt && Character.isJavaIdentifierStart(ch)) {
					fScanLocation.setLineNo(fLineno);
					String id = readIdentifier(ch);
					
					if (id != null) {
						if (id.equals("package")) {
							ch = skipWhite_ll(get_ch_ll());
							String pkg = readIdentifier(ch);
						
							if (fObserver != null) {
								fObserver.enter_package(pkg);
							}
						} else if (id.equals("endpackage")) {
							if (fObserver != null) {
								fObserver.leave_package();
							}
						}
					}
				}
				new_stmt = false;
			}
		}
		
		if (fObserver != null) {
			fObserver.leave_file();
		}
	}
	
	private String readIdentifier(int ci) {

		fTmpBuffer.setLength(0);
		
		if (!Character.isJavaIdentifierStart(ci)) {
			unget_ch(ci);
			return null;
		}

		fTmpBuffer.append((char)ci);

		while ((ci = get_ch_ll()) != -1 && 
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

		if (fTmpBuffer.length() == 0) {
			return null;
		} else {
			return fTmpBuffer.toString();
		}
	}

	private String readLine_ll(int ci) {
		int last_ch = -1;
		
		fTmpBuffer.setLength(0);
		while (ci != -1 && ci != '\n' || last_ch == '\\') {
			if (last_ch == '\\' && ci == '\n') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\r') {
					fTmpBuffer.setLength(fTmpBuffer.length()-1);
				}
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, '\n');
				}
			} else {
				fTmpBuffer.append((char)ci);
			}

			if (ci != '\r') {
				last_ch = ci;
			}

			ci = get_ch_ll();
		}

		if (fTmpBuffer.length() == 0) {
			return null;
		} else {
			return fTmpBuffer.toString();
		}
	}
	
	public String readString_ll(int ci) {
		
		fTmpBuffer.setLength(0);
		int last_ch = -1;
		
		if (ci != '"') {
			return null;
		}
		
		ci = get_ch_ll();
		while ((ci != '"' && ci != '\n') || last_ch == '\\') {
			if (last_ch == '\\' && ci == '"') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, '"');
				}
			} else if (last_ch == '\\' && ci == '\n') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\r') {
					fTmpBuffer.setLength(fTmpBuffer.length()-1);
				}
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, ' ');
				}
			} else {
				fTmpBuffer.append((char)ci);
			}
			
			if (ci != '\r') {
				last_ch = ci;
			}
			
			ci = get_ch_ll();
		}
		
		return fTmpBuffer.toString();
	}

	private void handle_preproc_directive(String type) {
		int ch = -1;
		
		fScanLocation.setLineNo(fLineno);

		if (type.equals("ifdef") || type.equals("ifndef")) {
			fPPBuffer.setLength(0);
			
			ch = skipWhite_ll(get_ch_ll());
			
			// TODO: evaluate the expression?
			readLine_ll(ch);
			
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
			String def_id = null;

			// Push the line number up to the scanner
			/*
			if (fScanner != null) {
				fScanner.setStmtLocation(getLocation());
			}
			 */

			ch = skipWhite_ll(get_ch_ll());
			
			def_id = readIdentifier(ch);
//			System.out.println("    `define \"" + def_id + "\"");

			fParamList.clear();
			
			if ((ch = get_ch_ll()) == '(') {
				// Has parameters
				
				do {
					ch = skipWhite_ll(get_ch_ll());
					
					if (!(Character.isJavaIdentifierPart(ch))) {
						break;
					} else {
						String p = readIdentifier(ch);
						fParamList.add(p);
					}
					
					ch = skipWhite_ll(get_ch_ll());
				} while (ch == ',');
			}

			// Now, read the remainder of the definition
			String define = readLine_ll(ch);
			
			if (fObserver != null) {
				fObserver.preproc_define(def_id, params, define);
			}
		} else if (type.equals("include")) {
			ch = skipWhite_ll(get_ch_ll());

			if (ch == '"') {
				String inc = readString_ll(ch);

//				System.out.println("Include \"" + inc + "\"");
				if (fObserver != null) {
					fObserver.preproc_include(inc);
				}
			}
		} else {
			// macro expansion. We can just ignore this

			readLine_ll(get_ch_ll());
		}
	}
	
	public int skipWhite_ll(int ch) {

		// Skip whitespace. Consider the line-continuation character as WS
		while (Character.isWhitespace(ch) || ch == '\\') {
			int tmp = get_ch_ll();
			
			if (ch == '\\' && (tmp != '\r' && tmp != '\n')) {
				unget_ch(tmp);
				return ch;
			}
			ch = tmp;
		}
		
		return ch;
	}
	
	private int get_ch() {
		int ch = -1;
		
		do {
			ch = get_ch_pp();
		} while (!fPreProcEn.peek() && ch != -1);
		
		return ch;
	}

	private int get_ch_pp() {
		int ch=-1;

		do {
			ch = get_ch_ll();

			if (ch == '/') {
				int ch2 = get_ch_ll();

				if (ch2 == '/') {
					while ((ch = get_ch_ll()) != -1 && ch != '\n') {}
				} else if (ch2 == '*') {
					int end_comment[] = {-1, -1};

					while ((ch = get_ch_ll()) != -1) {
						end_comment[0] = end_comment[1];
						end_comment[1] = ch;

						if (end_comment[0] == '*' && end_comment[1] == '/') {
							break;
						}
					}

					ch = ' ';
				} else {
					unget_ch(ch2);
				}
			} else if (ch == '`') {
				ch = get_ch_ll();
				
				String type = readIdentifier(ch);
				
				handle_preproc_directive(type);

				continue;
			} /* else if (ch == '"') {
				int ch_l = -1;
				
				// skip strings
				while ((ch = get_ch_ll()) != -1 &&
						ch != '"' && ch_l != '\\') {
					ch_l = ch;
				}
			} */
		} while (false);
		
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
			fInputBufferIdx = 0;
			fInputBufferMax = -1;
			try {
				fInputBufferMax = fInput.read(
						fInputBuffer, 0, fInputBuffer.length);
			} catch (IOException e) {
			}
		}
		
		if (fInputBufferIdx < fInputBufferMax) {
			ch = fInputBuffer[fInputBufferIdx++];
		}
		
		if (fLastCh == '\n') {
			fLineno++;
		}
		fLastCh = ch;
		
		return ch;
	}
	
	private void unget_ch(int ch) {
		fUngetCh = ch;
	}
}

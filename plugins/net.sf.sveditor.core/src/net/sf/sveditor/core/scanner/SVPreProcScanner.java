package net.sf.sveditor.core.scanner;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class SVPreProcScanner implements ISVScanner {
	private InputStream			fInput;
	private String				fFileName;
	private boolean				fExpandMacros;
	
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
	private ISVScanner			fScanner;
	private IDefineProvider		fDefineProvider;
	private ScanLocation		fScanLocation;

	
	public SVPreProcScanner() {
		fPPBuffer  = new StringBuffer();
		fTmpBuffer = new StringBuffer();
		fPreProcEn = new Stack<Boolean>();
		fParamList = new ArrayList<String>();
		fScanLocation = new ScanLocation("", 0, 0);
		fExpandMacros = false;
	}
	
	public void setExpandMacros(boolean expand_macros) {
		fExpandMacros = expand_macros;
	}
	
	public void setObserver(ISVScannerObserver observer) {
		fObserver = observer;
		fObserver.init(this);
	}
	
	public void setDefineProvider(IDefineProvider def_provider) {
		fDefineProvider = def_provider;
	}
	
	public void setScanner(ISVScanner scanner) {
		fScanner = scanner;
	}
	
	@Override
	public ScanLocation getStmtLocation() {
		return fScanLocation;
	}
	
	public ScanLocation getLocation() {
		return new ScanLocation(fFileName, fLineno, 0);
	}

	@Override
	public void setStmtLocation(ScanLocation location) {
		// Do nothing
	}
	
	public void init(InputStream in, String name) {
		fLineno = 1;
		fScanLocation.setLineNo(1);
		
		fPPBuffer.setLength(0);
		fTmpBuffer.setLength(0);
		fPreProcEn.clear();
		
		fPreProcEn.push(true);
		
		fInput    = in;
		fFileName = name;
		
		fScanLocation.setFileName(name);
	}

	public void scan() {
		int     ch;
		boolean new_stmt = true;
		
		System.out.println("--> Scan file \"" + fFileName + "\"");
		
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
							ch = skipWhite(get_ch());
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
		
		System.out.println("<-- Scan file \"" + fFileName + "\"");
	}
	
	private String readIdentifier(int ci) {

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

		if (fTmpBuffer.length() == 0) {
			return null;
		} else {
			return fTmpBuffer.toString();
		}
	}

	private String readIdentifier_ll(int ci) {

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
		
		unget_ch(ci);

		if (fTmpBuffer.length() == 0) {
			return null;
		} else {
			return fTmpBuffer.toString();
		}
	}
	
	private String readString(int ci) {
		
		fTmpBuffer.setLength(0);
		int last_ch = -1;
		
		if (ci != '"') {
			return null;
		}
		
		ci = get_ch();
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
			
			ci = get_ch();
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
			String remainder = readLine_ll(ch);
			
			if (type.equals("ifdef")) {
				System.out.println("ifdef \"" + remainder + "\"");
				fPreProcEn.push(false);
			} else {
				System.out.println("ifndef \"" + remainder + "\"");
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
			readLine_ll(skipWhite_ll(get_ch_ll()));
		} else if (type.equals("begin_keywords") || type.equals("end_keywords")) {
			// TODO: read to line-end 
			readLine_ll(skipWhite_ll(get_ch_ll()));
		} else if (type.equals("define")) {
			String def_id = null;

			// Push the line number up to the scanner
			if (fScanner != null) {
				fScanner.setStmtLocation(getStmtLocation());
			}

			ch = skipWhite_ll(get_ch_ll());
			
			def_id = readIdentifier_ll(ch);
			
			if (def_id.equals("ovm_object_utils_end")) {
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
//			System.out.println("    `define \"" + def_id + "\"");

			fParamList.clear();
			
			ch = get_ch_ll();
			
			if (ch == '(') {
				// Has parameters
				
				do {
					ch = skipWhite_ll(get_ch_ll());
					
					if (!(Character.isJavaIdentifierPart(ch))) {
						break;
					} else {
						String p = readIdentifier_ll(ch);
						fParamList.add(p);
					}
					
					ch = skipWhite_ll(get_ch_ll());
				} while (ch == ',');
				
				if (ch == ')') {
					ch = get_ch_ll();
				}
			}

			// Now, read the remainder of the definition
			String define = readLine_ll(ch);
			
			System.out.println("Define: " + def_id + "(" + fParamList.size() + ") " 
					+ define);
			if (fPreProcEn.peek()) {
				if (fObserver != null) {
					fObserver.preproc_define(def_id, fParamList, define);
				}
			}
		} else if (type.equals("include")) {
			ch = skipWhite_ll(get_ch_ll());

			if (ch == '"') {
				String inc = readString(ch);

//				System.out.println("Include \"" + inc + "\"");
				if (fPreProcEn.peek()) {
					if (fObserver != null) {
						fObserver.preproc_include(inc);
					}
				}
			}
		} else {
			// macro expansion. 
			ch = get_ch_ll();

			fParamList.clear();
			if (ch == '(') {
				// Has parameters -- the remainder of the macro invocation
				do {
					ch = skipWhite_ll(get_ch_ll());
					
					if (!(Character.isJavaIdentifierPart(ch))) {
						break;
					} else {
						String p = readIdentifier_ll(ch);
						fParamList.add(p);
					}
					
					ch = skipWhite_ll(get_ch_ll());
				} while (ch == ',');
			}
			
			if (fDefineProvider != null && fExpandMacros && fPreProcEn.peek()) {
				System.out.println("Expand macro \"" + type + "\" w/" + 
						fParamList.size() + " parameters");
				String val = fDefineProvider.getDefineVal(type, fParamList);
				
				System.out.println("expansion: " + val);
			}
		}
	}
	
	private int skipWhite(int ch) {

		// Skip whitespace. Consider the line-continuation character as WS
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

	private int skipWhite_ll(int ch) {

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

	public int get_ch() {
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
				
				String type = readIdentifier_ll(ch);
				
				if (type != null) {
					handle_preproc_directive(type);
				} else {
					System.out.println("null type @ " + 
							fFileName + ":" + fLineno);
					try {
						throw new Exception();
					} catch (Exception e) {
						e.printStackTrace();
					}
				}

				continue;
			}
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

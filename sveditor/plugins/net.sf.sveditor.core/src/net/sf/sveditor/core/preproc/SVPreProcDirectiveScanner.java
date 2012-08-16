/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.preproc;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.ISVPreProcScannerObserver;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcDirectiveScanner extends AbstractTextScanner 
	implements ISVScanner {
	
	private InputStream						fInput;
	private String							fFileName;
	private boolean						fInProcess;
	
	private int							fUngetCh = -1;
	private int							fLastCh  = -1;
	private int							fLineno;
	private StringBuffer					fTmpBuffer;
	private StringBuilder					fCommentBuffer;
	private boolean						fInComment;
	private List<Tuple<String, String>>		fParamList;
	private ISVPreProcScannerObserver		fObserver;
	private ISVScanner						fScanner;
	private IDefineProvider					fDefineProvider;
	private ScanLocation					fScanLocation;
	private IDocCommentParser   			fDocCommentParser;
	private byte							fInBuffer[];
	private int							fInBufferIdx;
	private int							fInBufferMax;
	public static final Set<String>		fIgnoredDirectives;
	private static LogHandle				fLog = LogFactory.getLogHandle("SVPreProcDirectiveScanner");
	
	static {
		fIgnoredDirectives = new HashSet<String>();
		fIgnoredDirectives.add("begin_keywords");
		fIgnoredDirectives.add("celldefine");
		fIgnoredDirectives.add("default_nettype");
		fIgnoredDirectives.add("end_keywords");
		fIgnoredDirectives.add("endcelldefine");
		fIgnoredDirectives.add("protect");
		fIgnoredDirectives.add("endprotect");
		// Ignored for now
		fIgnoredDirectives.add("line");
		fIgnoredDirectives.add("nounconnected_drive");
		fIgnoredDirectives.add("timescale");
		// Ignored for now
		fIgnoredDirectives.add("resetall");
		fIgnoredDirectives.add("unconnected_drive");
		// Ignored for now
		fIgnoredDirectives.add("undef");
		fIgnoredDirectives.add("undefineall");
	}

	
	public SVPreProcDirectiveScanner() {
		fTmpBuffer = new StringBuffer();
		fParamList = new ArrayList<Tuple<String,String>>();
		fScanLocation = new ScanLocation("", 0, 0);
		fCommentBuffer = new StringBuilder();
		fDocCommentParser = new DocCommentParser();
		fInComment = false;
		fInBuffer = new byte[1024*8];
		fInBufferIdx = 0;
		fInBufferMax = 0;
	}
	
	public void setObserver(ISVPreProcScannerObserver observer) {
		fObserver = observer;
		fObserver.init(this);
	}
	
	public void setDefineProvider(IDefineProvider def_provider) {
		fDefineProvider = def_provider;
	}
	
	public void setScanner(ISVScanner scanner) {
		fScanner = scanner;
	}
	
	public ScanLocation getStmtLocation() {
		return fScanLocation;
	}
	
	public ScanLocation getStartLocation() {
		return fScanLocation;
	}
	
	public ScanLocation getLocation() {
		return new ScanLocation(fFileName, fLineno, 0);
	}

	public void setStmtLocation(ScanLocation location) {
		// Do nothing
	}
	
	public void init(InputStream in, String name) {
		fLineno = 1;
		fScanLocation.setLineNo(1);
		
		fTmpBuffer.setLength(0);

		fInput    = in;
		fFileName = name;
		
		fScanLocation.setFileName(name);
	}
	
	public void close() {
		try {
			if (fInput != null) {
				fInput.close();
			}
		} catch (IOException e) {}
	}

	public void process() {
		int				ch, last_ch = -1;
		int				end_comment[] = {-1, -1};
		boolean			in_string = false;
//		StringBuilder	comment_buffer = new StringBuilder();
//		boolean			in_comment_section = false;
		boolean			foundSingleLineComment = false;
		
		fInProcess = true;
		
		if (fObserver != null) {
			fObserver.enter_file(fFileName);
		}
		
		while ((ch = get_ch()) != -1) {
			foundSingleLineComment = false ;
			if (!in_string) {
				// Handle comment
				if (ch == '/') {
					int ch2 = get_ch();

					if (ch2 == '/') {
						foundSingleLineComment = true ;
//						fCommentBuffer.append("//");
						beginComment();
						while ((ch = get_ch()) != -1 && ch != '\n') { 
							fCommentBuffer.append((char)ch);
						}
//						in_comment_section = true;
						fCommentBuffer.append('\n');
						ch = ' ';
						last_ch = ' ';
					} else if (ch2 == '*') {
						end_comment[0] = -1;
						end_comment[1] = -1;
						beginComment();
//						fCommentBuffer.append("/*");
						while ((ch = get_ch()) != -1) {
							end_comment[0] = end_comment[1];
							end_comment[1] = ch;

							fCommentBuffer.append((char)ch);

							if (end_comment[0] == '*' && end_comment[1] == '/') {
								endComment() ;
								break;
							} else {
								fCommentBuffer.append((char)ch);
							}
//							in_comment_section = true;
						}
						ch = ' ';
						last_ch = ' ';
					} else {
						unget_ch(ch2);
					}
				}

				if (!Character.isWhitespace(ch) && fInComment) {
					// Send accumulated comment to observer
					// TODO: handle setting correct line
//					if (fObserver != null) {
//						fObserver.comment("",comment_buffer.toString());
//					}
					endComment() ;
//					comment_buffer.setLength(0);
//					in_comment_section = false;
				}
				
				if (ch == '`') {
					handle_preproc_directive();
				} else {
					if (ch == '"' && last_ch != '\\') {
						// Enter string
						in_string = true;
					}
				}
			} else {
				// In String
				if (ch == '"' && last_ch != '\\') {
					in_string = false;
				}
			}
			last_ch = ch;
			
			if(fInComment && !foundSingleLineComment && ((char)ch) == '\n') { endComment() ; }
		
		}
		
		if (fObserver != null) {
			fObserver.leave_file();
		}
		
		fInProcess = false;
	}
	
	private void beginComment() {
		if(!fInComment){ fCommentBuffer.setLength(0) ; }
		fInComment = true ; 
	}
	
	private void endComment() {
		if(!fInComment) { return ; }
		fInComment = false ;
		String comment = fCommentBuffer.toString() ;
		String title = fDocCommentParser.isDocComment(comment) ;
		if(title != null) { 
			if(fObserver != null) { fObserver.comment( title, comment) ; }
		}
	}	
	
	private String readLine(int ci) {
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

			ci = get_ch();
		}
		
		unget_ch(ci);

		if (fTmpBuffer.length() == 0) {
			return null;
		} else {
			return fTmpBuffer.toString();
		}
	}

	private String readString_ll(int ci) {
		
		fTmpBuffer.setLength(0);
		int last_ch = -1;
		
		if (ci != '"') {
			return null;
		}
		
		fTmpBuffer.append((char)ci);
		
		ci = get_ch();
		while ((ci != '"' && ci != '\n' && ci != -1) || last_ch == '\\') {
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

		if (ci != -1) {
			fTmpBuffer.append((char)ci);
		}
		
		return fTmpBuffer.toString();
	}

	private void handle_preproc_directive() {
		int ch = -1;
		
		// Skip any whitespace (up to end-of-line) between
		// the ` and the directive
		while ((ch = get_ch()) != -1 && 
				Character.isWhitespace(ch) && ch != '\n') { }
		
		if (ch == -1) {
			return;
		}
	
		String type = readIdentifier(ch);
		
		if (type == null) {
			type = "";
		}

		fScanLocation.setLineNo(fLineno);

		if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
			ch = skipWhite(get_ch());
			
			// TODO: evaluate the expression?
			// String remainder = readLine_ll(ch).trim();
			String remainder = readIdentifier(ch);
			
			if (remainder != null) {
				remainder = remainder.trim();
			} else {
				remainder = "";
			}
			
			if (fObserver != null) {
				if (type.equals("elsif")) {
					fObserver.leave_preproc_conditional();
				}
				fObserver.enter_preproc_conditional(type, remainder);
			}
		} else if (type.equals("else")) {
			if (fObserver != null) {
				fObserver.leave_preproc_conditional();
				fObserver.enter_preproc_conditional("else", "");
			}
		} else if (type.equals("endif")) {
			if (fObserver != null) {
				fObserver.leave_preproc_conditional();
			}
		} else if (fIgnoredDirectives.contains(type)) {
			// Skip entire line 
			readLine(get_ch());
		} else if (type.equals("define")) {
			String def_id = null;

			// Push the line number up to the scanner
			if (fScanner != null) {
				fScanner.setStmtLocation(getStmtLocation());
			}

			ch = skipWhite(get_ch());
			
			def_id = readIdentifier(ch);
			
			fParamList.clear();
			
			ch = get_ch();
			
			if (ch == '(') {
				// Has parameters
				
				do {
					ch = skipWhite(get_ch());
					
					if (!(Character.isJavaIdentifierPart(ch))) {
						break;
					} else {
						String p = readIdentifier(ch);
						String dflt = null;
						
						ch = skipWhite(get_ch());
						
						if (ch == '=') {
							// Read default value
							ch = skipWhite(get_ch());
							if (ch == '"') {
								// String
								dflt = readString(ch);
								dflt = "\"" + dflt + "\"";
							} else {
								// Read up to comma or close bracket
								startCapture(ch);
								while ((ch = get_ch()) != -1 && ch != ',' && ch != ')') { }
								unget_ch(ch);
								dflt = endCapture();
							}
						} else {
							unget_ch(ch);
						}
						fParamList.add(new Tuple<String, String>(p, dflt));
					}
					
					ch = skipWhite(get_ch());
				} while (ch == ',');
				
				if (ch == ')') {
					ch = get_ch();
				}
			}

			// Now, read the remainder of the definition
			String define = readLine(ch);
			
			if (define == null) {
				define = ""; // define this macro as existing
			}

			/* We should carry-through the single-line comments. However, this is only
			 * true in the case of a single-line macro. Multi-line macros get to keep
			 * their single-line comments
			 */ 
			int last_comment;
			if ((last_comment = define.lastIndexOf("//")) != -1) {
				int lr = define.indexOf('\n', last_comment);
				if (lr == -1) {
					// Nothing beyond this comment
					define = define.substring(0, define.indexOf("//"));
				}
			}
			
			if (fObserver != null) {
				fObserver.preproc_define(def_id, fParamList, define);
			}
		} else if (type.equals("include")) {
			ch = skipWhite(get_ch());
			
			if (ch == '"') {
				String inc = readString_ll(ch);
				
				inc = inc.substring(1, inc.length()-1);
				
				if (fObserver != null) {
					fObserver.preproc_include(inc);
				}
			}
		} else if (type.equals("__LINE__")) {
		} else if (type.equals("__FILE__")) {
		} else if (type.equals("pragma")) {
			ch = skipWhite(get_ch());
			String id = readIdentifier(ch);
			
			if (id != null) {
				// Ignore everything in the 'protected' region. 
				// Not much we can meaningfully show...
				if (id.equals("protect")) {
					ch = skipWhite(get_ch());
					
					id = readIdentifier(ch);
				}
			}
		} else if (type.equals("protected")) {
		} else if (type.equals("endprotected")) {
		} else {
			// macro expansion.
			// TODO: is TmpBuffer available?
			fTmpBuffer.setLength(0);
			
			fTmpBuffer.append('`');
			fTmpBuffer.append(type);

			// If we're in a disabled section, don't try to expand
				// Read the full string

			boolean is_defined = (fDefineProvider != null)?fDefineProvider.isDefined(type, fLineno):false;
			if (fDefineProvider != null && 
					(fDefineProvider.hasParameters(type, fLineno) || !is_defined)) {
				// Try to read the parameter list
				ch = get_ch();
				// skip up to new-line or non-whitespace
				while (ch != -1 && Character.isWhitespace(ch) && ch != '\n') {
					ch = get_ch();
				}
				// ch = skipWhite(ch);

				if (ch == '(') {
					fTmpBuffer.append((char)ch);

					int matchLevel=1;

					do {
						ch = get_ch();

						if (ch == '(') {
							matchLevel++;
						} else if (ch == ')') {
							matchLevel--;
						}

						if (ch != -1) {
							fTmpBuffer.append((char)ch);
						}
					} while (ch != -1 && matchLevel > 0);
				} else if (is_defined) {
					fDefineProvider.error("macro \"" + type +
							"\" should have parameters, but doesn't", 
							fScanLocation.getFileName(),
							fScanLocation.getLineNo());
					fLog.debug("[ERROR] macro \"" + type + 
							"\" should have parameters, but doesn't @ " +
							fScanLocation.getFileName() + ":" + 
							fScanLocation.getLineNo());
					unget_ch(ch);
				} else {
					unget_ch(ch);
				}
			}
		}
	}
	
	public int get_ch() {
		int ch = -1;
		
		if (!fInProcess) {
			throw new RuntimeException(
					"SVPreProcDirectiveScanner.get_ch() cannot be called externally");
		}
		
		if (fUngetCh != -1) {
			ch = fUngetCh;
			fUngetCh = -1;
		} else {
			if (fInBufferIdx >= fInBufferMax) {
				// Time to read more data
				try {
					fInBufferMax = fInput.read(fInBuffer, 0, fInBuffer.length);
					fInBufferIdx = 0;
				} catch (IOException e) {}
			}
			if (fInBufferIdx < fInBufferMax) {
				ch = fInBuffer[fInBufferIdx++];
			} else {
				ch = -1;
			}
			if (fLastCh == '\n') {
				fLineno++;
			}
			fLastCh = ch;
		}

		if (ch != -1 && fCaptureEnabled) {
			fCaptureBuffer.append((char)ch);
		}

		return ch;
	}

	public void unget_ch(int ch) {
		fUngetCh = ch;

		if (ch != -1 && fCaptureEnabled && fCaptureBuffer.length() > 0) {
			fCaptureBuffer.deleteCharAt(fCaptureBuffer.length()-1);
		}
	}

	// Unused
	public long getPos() {
		return -1;
	}
	
}

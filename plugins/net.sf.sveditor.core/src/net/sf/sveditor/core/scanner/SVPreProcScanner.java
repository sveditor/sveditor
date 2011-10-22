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


package net.sf.sveditor.core.scanner;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcScanner implements ISVScanner {
	
	private static final int    PP_DISABLED 			= 0;
	private static final int    PP_ENABLED  			= 1;
	
	// This bit is set when we are within a disabled section.
	// It's impossible for anything in a sub-section to be enabled
	private static final int    PP_CARRY    			= 2;
	
	// This bit is set when a block within this level of conditionals
	// has been taken (ie `ifdef (true) ... ; `ifndef (false))
	private static final int	PP_THIS_LEVEL_EN_BLOCK 	= 4;
	
	private InputStream			fInput;
	private String				fFileName;
	private boolean				fExpandMacros;
	private boolean				fEvalConditionals;
	
	private byte				fInputBuffer[] = new byte[1024 * 1024];
	private int					fInputBufferIdx = 0;
	private int					fInputBufferMax = 0;
	private int					fUngetCh = -1;
	private int					fUngetCh2 = -1;
	private int					fLastCh  = -1;
	private int					fLineno;
	private StringBuffer		fPPBuffer;
	private StringBuffer		fTmpBuffer;
	private Stack<Integer>		fPreProcEn;
	private List<String>		fParamList;
	private ISVPreProcScannerObserver	fObserver;
	private ISVScanner			fScanner;
	private IDefineProvider		fDefineProvider;
	private ScanLocation		fScanLocation;
	private StringBuffer		fUnaccBuffer;
	private boolean				fInString;
	private int					fLastChPP;
	private static final Set<String>	fIgnoredDirectives;
	private static LogHandle	fLog = LogFactory.getLogHandle("SVPreProcScanner");
	
	static {
		fIgnoredDirectives = new HashSet<String>();
		fIgnoredDirectives.add("begin_keywords");
		fIgnoredDirectives.add("celldefine");
		fIgnoredDirectives.add("default_nettype");
		fIgnoredDirectives.add("end_keywords");
		fIgnoredDirectives.add("endcelldefine");
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

	
	public SVPreProcScanner() {
		fPPBuffer  = new StringBuffer();
		fTmpBuffer = new StringBuffer();
		fUnaccBuffer = new StringBuffer();
		fPreProcEn = new Stack<Integer>();
		fParamList = new ArrayList<String>();
		fScanLocation = new ScanLocation("", 0, 0);
		fExpandMacros     = false;
		fEvalConditionals = false;
		fInString         = false;
		fLastChPP         = -1;
	}
	
	public void setExpandMacros(boolean expand_macros) {
		fExpandMacros = expand_macros;
	}
	
	public void setEvalConditionals(boolean eval_conditionals) {
		fEvalConditionals = eval_conditionals;
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
		
		fPPBuffer.setLength(0);
		fTmpBuffer.setLength(0);
		fPreProcEn.clear();

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

	public void scan() {
		int     ch;
		boolean new_stmt = true;
		
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

	private String readPreProcId_ll(int ci) {

		fTmpBuffer.setLength(0);
		
		if (!Character.isJavaIdentifierStart(ci)) {
			unget_ch(ci);
			return null;
		}

		fTmpBuffer.append((char)ci);

		while ((ci = get_ch_ll()) != -1 && (SVCharacter.isSVIdentifierPart(ci))) {
			fTmpBuffer.append((char)ci);
		}
		unget_ch(ci);

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

	private String readString_ll(int ci) {
		
		fTmpBuffer.setLength(0);
		int last_ch = -1;
		
		if (ci != '"') {
			return null;
		}
		
		fTmpBuffer.append((char)ci);
		
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

		if (ci != -1) {
			fTmpBuffer.append((char)ci);
		}
		
		return fTmpBuffer.toString();
	}

	private void handle_preproc_directive(String type) {
		int ch = -1;
		
		fScanLocation.setLineNo(fLineno);

		if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
			fPPBuffer.setLength(0);
			
			ch = skipWhite_ll(get_ch_ll());
			
			// TODO: evaluate the expression?
			String remainder = readLine_ll(ch).trim();
			
			if (fEvalConditionals) {
				if (type.equals("ifdef")) {
					if (fDefineProvider != null) {
						enter_ifdef(fDefineProvider.isDefined(
								remainder, fLineno));
					} else {
						enter_ifdef(false);
					}
				} else if (type.equals("ifndef")) {
					if (fDefineProvider != null) {
						enter_ifdef(!fDefineProvider.isDefined(
								remainder, fLineno));
					} else {
						enter_ifdef(true);
					}
				} else { // elsif
					if (fDefineProvider != null) {
						enter_elsif(fDefineProvider.isDefined(
								remainder, fLineno));
					} else {
						enter_elsif(false);
					}
				}
			} else {
				if (fObserver != null) {
					fObserver.enter_preproc_conditional(type, remainder);
				}
			}
		} else if (type.equals("else")) {
			if (fEvalConditionals) {
				enter_else();
			} else {
				if (fObserver != null) {
					fObserver.leave_preproc_conditional();
					fObserver.enter_preproc_conditional("else", "");
				}
			}
		} else if (type.equals("endif")) {
			if (fEvalConditionals) {
				leave_ifdef();
			} else {
				if (fObserver != null) {
					fObserver.leave_preproc_conditional();
				}
			}
		} else if (fIgnoredDirectives.contains(type)) {
			// Skip entire line 
			readLine_ll(get_ch_ll());
		} else if (type.equals("define")) {
			String def_id = null;

			// Push the line number up to the scanner
			if (fScanner != null) {
				fScanner.setStmtLocation(getStmtLocation());
			}

			ch = skipWhite_ll(get_ch_ll());
			
			def_id = readIdentifier_ll(ch);
			
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
			
			if (ifdef_enabled()) {
				if (fObserver != null) {
					/*
					System.out.println(getLocation().getFileName() + ":" + 
							getLocation().getLineNo() + " Define \"" + def_id + "\"");
					 */
					fObserver.preproc_define(def_id, fParamList, define);
				}
			}
		} else if (type.equals("include")) {
			ch = skipWhite_ll(get_ch_ll());
			
			if (ch == '"') {
				String inc = readString_ll(ch);
				
				inc = inc.substring(1, inc.length()-1);
				
				if (ifdef_enabled()) {
					if (fObserver != null) {
						fObserver.preproc_include(inc);
					}
				}
			}
		} else if (type.equals("__LINE__")) {
			if (fExpandMacros) {
				push_unacc("" + getLocation().getLineNo());
			}
		} else if (type.equals("__FILE__")) {
			if (fExpandMacros) {
				push_unacc("\"" + fFileName + "\"");
			}
		} else if (type.equals("pragma")) {
			ch = skipWhite_ll(get_ch_ll());
			String id = readIdentifier_ll(ch);
			
			if (id != null) {
				// Ignore everything in the 'protected' region. 
				// Not much we can meaningfully show...
				if (id.equals("protect")) {
					ch = skipWhite_ll(get_ch_ll());
					
					id = readIdentifier_ll(ch);
					
					if (id != null) {
						if (id.equals("begin_protected")) {
							enter_ifdef(false);
						} else if (id.equals("end_protected")) {
							leave_ifdef();
						}
					}
				}
			}
		} else if (type.equals("protected")) {
			enter_ifdef(false);
		} else if (type.equals("endprotected")) {
			leave_ifdef();
		} else {
			// macro expansion.
			// TODO: is TmpBuffer available?
			fTmpBuffer.setLength(0);
			
			fTmpBuffer.append('`');
			fTmpBuffer.append(type);

			// If we're in a disabled section, don't try to expand
			if (ifdef_enabled()) {
				// Read the full string

				boolean is_defined = (fDefineProvider != null)?fDefineProvider.isDefined(type, fLineno):false;
				if (fDefineProvider != null && 
						(fDefineProvider.hasParameters(type, fLineno) || !is_defined)) {
					// Try to read the parameter list
					ch = get_ch_ll();
					// skip up to new-line or non-whitespace
					while (ch != -1 && Character.isWhitespace(ch) && ch != '\n') {
						ch = get_ch_ll();
					}
					// ch = skipWhite_ll(ch);

					if (ch == '(') {
						fTmpBuffer.append((char)ch);

						int matchLevel=1;

						do {
							ch = get_ch_ll();

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

				if (fDefineProvider != null) {
					if (fExpandMacros) {
						try {
							push_unacc(fDefineProvider.expandMacro(
									fTmpBuffer.toString(), 
									getLocation().getFileName(),
									getLocation().getLineNo()));
						} catch (Exception e) {
							System.out.println("Exception while expanding \"" + 
									fTmpBuffer.toString() + "\" @ " +
									getLocation().getFileName() + ":" + 
									getLocation().getLineNo());
							e.printStackTrace();
						}
					}
				}
			}
		}
	}
	
	private void enter_ifdef(boolean enabled) {
		int e = (enabled)?PP_ENABLED:PP_DISABLED;
		
		if (fPreProcEn.size() > 0) {
			int e_t = fPreProcEn.peek();
			
			if ((e_t & PP_ENABLED) == 0) {
				// Anything beneath a disabled section is also disabled
				e = PP_DISABLED;
				e |= PP_CARRY;
			}
		}
		
		// Mark that we've taken one branch
		if ((e & PP_ENABLED) == 1) {
			e |= PP_THIS_LEVEL_EN_BLOCK;
		}
		
		fPreProcEn.push(e);
	}
	
	private void leave_ifdef() {
		if (fPreProcEn.size() > 0) {
			fPreProcEn.pop();
		}
	}
	
	private void enter_elsif(boolean enabled) {
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();

			if (enabled) {
				// Condition evaluates true
				if ((e & PP_CARRY) != PP_CARRY && 
						(e & PP_THIS_LEVEL_EN_BLOCK) != PP_THIS_LEVEL_EN_BLOCK) {
					// Enable this branch
					e |= (PP_ENABLED | PP_THIS_LEVEL_EN_BLOCK);
				}
			} else {
				// Not enabled. Ensure the ENABLED flag is cleared
				e &= ~PP_ENABLED;
			}
			
			fPreProcEn.push(e);
		}
	}
	
	private void enter_else() {
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();
			
			// Invert only if we're in an enabled scope and
			// we haven't already 'taken' a branch in the 
			// ifdef/elsif/else structure
			if ((e & PP_CARRY) == 0) {
				
				if ((e & PP_THIS_LEVEL_EN_BLOCK) != 0) {
					// Disable any blocks beyond the 'taken' block
					e &= ~PP_ENABLED;
				} else {
					// Enable this branch and set the BLOCK_ENABLED flag
					e |= PP_ENABLED;
				}
			}
			
			// Flip to 'true' only if we aren't 
			fPreProcEn.push(e);
		}
	}
	
	private boolean ifdef_enabled() {
		if (fPreProcEn.size() == 0) {
			return true;
		} else {
			int e = fPreProcEn.peek();
			return ((e & PP_ENABLED) == PP_ENABLED);
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
		while ((Character.isWhitespace(ch) || ch == '\\') && ch != -1) {
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
		} while (!ifdef_enabled() && ch != -1);
		
		return ch;
	}

	private int get_ch_pp() {
		int ch=-1;

		while (true) {
			if (fUnaccBuffer.length() > 0) {
				ch = fUnaccBuffer.charAt(fUnaccBuffer.length()-1);
				fUnaccBuffer.setLength(fUnaccBuffer.length()-1);
			} else {
				ch = get_ch_ll();
			}
			
			if (ch == '/' && !fInString) {
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
			} else if (ch == '`' && !fInString) {
				ch = get_ch_ll();
				
				String type = readPreProcId_ll(ch);
				
				if (type != null) {
					handle_preproc_directive(type);
				} else {
					System.out.println("null type @ " + 
							fFileName + ":" + fLineno);
				}
				
				continue;
			}
			
			if (!fInString) {
				if (ch == '"' && fLastChPP != '\'') {
					fInString = true;
				}
			} else {
				if (ch == '"' && fLastChPP != '\\') {
					fInString = false;
				}
			}
			
			break;
		}

		if (fLastChPP == '\\' && ch == '\\') {
			fLastChPP = ' ';
		} else {
			fLastChPP = ch;
		}
		
		return ch;
	}
	
	private int get_ch_ll() {
		int ch = -1;
		int ch_l = -1;
		for (int i=0; i<2; i++) {
			
			if (fUngetCh != -1) {
				ch = fUngetCh;
				fUngetCh = fUngetCh2;
				fUngetCh2 = -1;
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
			
			if (ch != '\r' && ch_l != '\r') {
				break;
			} else if (ch_l == '\r' && ch != '\n') {
				unget_ch(ch);
				ch = '\n';
			}
			ch_l = ch;
		}
		return ch;
	}
	
	private void unget_ch(int ch) {
		if (fUngetCh == -1) {
			fUngetCh = ch;
		} else {
			fUngetCh2 = fUngetCh;
			fUngetCh = ch;
		}
	}
	
	private void push_unacc(String str) {
		StringBuilder tmp = new StringBuilder(str);
		if (fUnaccBuffer.length() == 0) {
			fUnaccBuffer.append(tmp.reverse());
		} else {
			fUnaccBuffer.insert(0, tmp.reverse());
		}
	}
}

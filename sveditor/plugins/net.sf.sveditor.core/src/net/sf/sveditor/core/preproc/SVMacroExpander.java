/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.preproc;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class SVMacroExpander extends AbstractTextScanner {
	
	private class Input {
		public ITextScanner				fScanner;
		public String					fName;
		
		public Input(String name, String str) {
			fName = name;
			fScanner = new StringTextScanner(str);
		}
		
		public String getFileName() { return fName; }
	}
	
	private static final int    PP_DISABLED 			= 0;
	private static final int    PP_ENABLED  			= 1;
	
	// This bit is set when we are within a disabled section.
	// It's impossible for anything in a sub-section to be enabled
	private static final int    PP_CARRY    			= 2;
	
	// This bit is set when a block within this level of conditionals
	// has been taken (ie `ifdef (true) ... ; `ifndef (false))
	private static final int	PP_THIS_LEVEL_EN_BLOCK 	= 4;	
	
	private static final boolean		fDebugEn				= false;
	private static final boolean		fDebugChEn				= false;
	private boolean						fDebugUndefinedMacros	= false;
	private String						fFilename;
	private int							fLineno;
	private Stack<Boolean>				fEnableOutputStack;
	private Stack<Integer>				fPreProcEn;	
	private LogHandle					fLog;
	private IPreProcMacroProvider		fMacroProvider;
	private List<IPreProcListener>		fListeners;
	private boolean						fHaveListeners;
	private Stack<Input>				fInputStack;
	private Input						fInputCurr;
	private StringBuilder				fOutput;

	public SVMacroExpander(IPreProcMacroProvider macro_provider) {
		fEnableOutputStack = new Stack<Boolean>();
		fLog = LogFactory.getLogHandle("SVPreProcDefineProvider");

		fMacroProvider  = macro_provider;
		
		fOutput = new StringBuilder();
		
		fListeners = new ArrayList<IPreProcListener>();
		fHaveListeners = false;
	}
	
	public void addPreProcListener(IPreProcListener l) {
		fListeners.add(l);
		fHaveListeners = true;
	}
	
	public void removePreProcListener(IPreProcListener l) {
		fListeners.remove(l);
		fHaveListeners = (fListeners.size() > 0);
	}
	
	private void error(String msg) {
		// TODO: route errors through IPreProcListener
//		for (IPreProcErrorListener l : fErrorListeners) {
//			l.preProcError(msg, filename, lineno);
//		}		
//		error(msg, fFilename, fLineno);
	}	

	public String expandMacro(
			String 			str,
			String 			filename,
			int 			lineno) {
		fOutput.setLength(0);
		fInputStack.clear();
		
		push_input(new Input("", str));
		
		fFilename = filename;
		fLineno   = lineno;
		

		if (fDebugEn) {
			debug("--> expandMacro(str): " + str);
		}
		
		if (fMacroProvider == null) {
			fLog.error("No macro provider specified");
			if (fDebugEn) {
				debug("<-- expandMacro(str): " + str);
				debug("    Result: \"\"");
			}
			return "";
		}

		fMacroProvider.setMacro("__FILE__", "\"" + fFilename + "\"");
		fMacroProvider.setMacro("__LINE__", "" + fLineno);
		fEnableOutputStack.clear();
		fEnableOutputStack.push(true);

		int ch, last_ch=-1;
		boolean in_string=false, ifdef_enabled=true;
		
		while ((ch = get_ch()) != -1) {
			
			if (!in_string) {
				if (ch == '/') {
					int ch2 = get_ch();
					
					if (ch2 == '/') {
						output(' ');
						while ((ch = get_ch()) != -1 && 
								ch != '\n' && ch != '\r') { 
							// TODO: could save the content 
						}
						
						if (ch == '\r') {
							ch = get_ch();
							if (ch != '\n') {
								unget_ch(ch);
							}
						}
						ch = '\n';
						last_ch = ' ';						
					} else if (ch2 == '*') {
						int end_comment1 = -1, end_comment2 = -1;

						output(' ');

						while ((ch = get_ch()) != -1) {
							end_comment1 = end_comment2;
							end_comment2 = ch;
							
							if (end_comment1 == '*' && end_comment2 == '/') {
								break;
							}
						}
						ch = ' ';
						last_ch = ' ';
					} else {
						unget_ch(ch2);
					}						
				}
				
				if (ch == '`') {
					// Processing an ifdef may affect enablement
					handle_preproc_directive();
					ifdef_enabled = ifdef_enabled();
					if (!ifdef_enabled) {
						output(' ');
					}
				} else {
					if (ch == '"' && last_ch != '\\') {
						// Enter string
						in_string = true;
					}
					if (ifdef_enabled) {
						output((char)ch);
					}
				}				
			} else {
				if (ch == '"' && last_ch != '\\') {
					in_string = false;
				}
				if (ifdef_enabled) {
					output((char)ch);
				}				
			}
			
			// Consecutive back-slashes convert to
			// a single backslash. For tracking purposes,
			// convert to space
			if (last_ch == '\\' && ch == '\\') {
				last_ch = ' ';
			} else {
				last_ch = ch;
			}			
		}
		
//		expandMacro();
		
		if (fDebugEn) {
			debug("<-- expandMacro(str): " + str);
			debug("    Result: " + fOutput.toString());
		}
	
		return fOutput.toString();
	}
	
	private void handle_preproc_directive() {
		int ch = -1;
		
		while ((ch = get_ch()) != -1 && Character.isWhitespace(ch)) { }
		long scan_loc = 0; // getLocation();
	
		String type;
		String buffer_macro_name = null;
		if (ch == -1) {
			type = "";
		} else {
			buffer_macro_name = (fInputCurr != null)?fInputCurr.getFileName():null;
			type = readPreProcIdentifier(ch);
	
			if (type == null) {
				type = "";
			}
		}
		
		if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
		
			// TODO: line number tracking
			ch = skipWhite(get_ch());
			
			// TODO: evaluate the expression?
			String remainder = readPreProcIdentifier(ch);
			
			if (remainder != null) {
				remainder = remainder.trim();
			} else {
				remainder = "";
			}
		
			// Add a new entry to the referenced macros 
//			add_macro_reference(remainder);

			SVDBMacroDef m = fMacroProvider.findMacro(remainder, -1);
			if (type.equals("ifdef")) {
				enter_ifdef(scan_loc, (m != null));
			} else if (type.equals("ifndef")) {
				enter_ifdef(scan_loc, (m == null));
			} else { // elsif
				enter_elsif(scan_loc, (m != null));
			}
		} else if (type.equals("else")) {
			enter_else(scan_loc);
		} else if (type.equals("endif")) {
			leave_ifdef(scan_loc);
//		} else if (fIgnoredDirectives.contains(type)) {
//			// Skip entire line 
//			readLine(get_ch());
		} else if (type.equals("define")) {
		} else if (type.equals("include")) {
		} else if (type.equals("__LINE__")) {
			if (ifdef_enabled()) {
				output("" + 1);
//TODO:				output("" + fInputCurr.getLineNo());
			}
		} else if (type.equals("__FILE__")) {
			if (ifdef_enabled()) {
				output("\"" + fInputCurr.getFileName() + "\"");
			}
		} else if (!type.equals("")) {
			// Note: type="" occurs when no identifier followed the tick
			// macro expansion.
			// TODO: is TmpBuffer available?
			fTmpBuffer.setLength(0);
			
			fTmpBuffer.append('`');
			fTmpBuffer.append(type);
		
			boolean skip_recursive =
					(buffer_macro_name != null && buffer_macro_name.equals("Macro: " + type)) /*||
					(fMacroExpSet.contains("Macro: " + type)) */;
			
			// If we're in a disabled section, don't try to expand
			if (skip_recursive) {
				// Omit input
			} else if (ifdef_enabled()) {
				// Read the full string
			
				// Add a reference for this macro
//				add_macro_reference(type);

				SVDBMacroDef m = fMacroProvider.findMacro(type, -1);
				if (m == null) {
					// TODO: produce error event 
				} 
				
				if (m == null || m.getParameters().size() > 0) {
					// TODO: need to actually extract parameters here
					
					// Try to read the parameter list
					ch = get_ch();
					
					// skip up to new-line or non-whitespace
					if (m == null) {
						// For undefined macros, only search up to end-of-line
						while (ch != -1 && Character.isWhitespace(ch) && ch != '\n') {
							ch = get_ch();
						}
					} else {
						// For defined macros, skip all whitespace
						while (ch != -1 && Character.isWhitespace(ch)) {
							ch = get_ch();
						}
					}

					if (ch == '(') {
						fTmpBuffer.append((char)ch);

						// Read the parameter list
						int matchLevel=1, last_ch = -1;
						boolean in_string = false;

						do {
							ch = get_ch();

							if (!in_string) {
								if (ch == '(') {
									matchLevel++;
								} else if (ch == ')') {
									matchLevel--;
								} else if (ch == '\"' && last_ch != '\\') {
									in_string = true;
								}
							} else if (ch == '\"' && last_ch != '\\') {
								in_string = false;
							}

							if (ch != -1) {
								// Found an escaped newline. Just get rid of it
								if (ch == '\n' && last_ch == '\\') {
									// Something to skip
									if (fTmpBuffer.length() > 0 && 
											fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\r') {
										// Remove extra line feed
										fTmpBuffer.setLength(fTmpBuffer.length()-1);
									}
									if (fTmpBuffer.length() > 0 && 
											fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
										// Remove escape char
										fTmpBuffer.setLength(fTmpBuffer.length()-1);
									}
								} else {
									fTmpBuffer.append((char)ch);
								}
							}
							last_ch = ch;
						} while (ch != -1 && matchLevel > 0);
					} else {
						unget_ch(ch);
					}
				}

				if (m == null) {
					// Leave a breadcrumb for the lexer
					output("`undefined"); // ??
				} else {
					if (m.getParameters().size() > 0) {
						fTmpBuffer.setLength(0);
						expandParameterRefs(new StringTextScanner(m.getDef()), 
								fTmpBuffer, null, null); 
//								fout, param_names, param_vals);
					} else {
						push_input(new Input("Macro: " + type, m.getDef()));
					}
				}
			}
			
		}
	}
	
	private static int skipPastMatchSkipStrings(
			StringBuilder	sb,
			ITextScanner 	scanner, 
			int 			ch1, 
			int 			ch2) {
		int ch;
		int lcnt=1, rcnt=0;
		
		while ((ch = scanner.get_ch()) != -1) {
			sb.append((char)ch);
			if (ch == ch1) {
				lcnt++;
			} else if (ch == ch2) {
				rcnt++;
			} else if (ch == '"') {
				skipPastString(sb, scanner);
			}
			if (lcnt == rcnt) {
				break;
			}
		}
		
		return scanner.get_ch();
	}
	
	private static void skipPastString(
			StringBuilder	sb,
			ITextScanner 	scanner) {
		int ch;
		int last_ch = -1;
		
		while ((ch = scanner.get_ch()) != -1) {
			sb.append((char)ch);
			if (ch == '"' && last_ch != '\\') {
				break;
			}
			if (last_ch == '\\' && ch == '\\') {
				// Don't count a double quote
				last_ch = -1;
			} else {
				last_ch = ch;
			}
		}
	}

	/**
	 * Extracts the elements of a macro call. 
	 * @param m
	 * @param scanner
	 * @param params
	 */
	public static void parseMacroCallParams(
			ITextScanner			scanner,
			List<String>			params) {
		StringBuilder sb = new StringBuilder();
		int idx = 0;
//		if (fDebugEn) {
//			debug("--> parse_params(" + m.getName() + ")");
//			debug("    str=" + scanner.getStorage().substring(scanner.getOffset()));
//		}
		int ch = scanner.get_ch(); // should enter on '('
		
		// Decide whether to parse parameters
		
//		for (int i=0; i<m.getParameters().size(); i++) {
		while (true) {
			sb.setLength(0);
			ch = scanner.skipWhite(ch);
			
			if (ch == '/') {
				int ch2 = scanner.get_ch();
				if (ch2 == '/') {
					while ((ch = scanner.get_ch()) != -1 && ch != '\n') { }
					ch = scanner.skipWhite(ch);
				} else if (ch2 == '*') {
					int c1=-1, c2=-1;
					while ((ch = scanner.get_ch()) != -1) {
						if (c1 == '*' && c2 == '/') {
							break;
						}
						c1 = c2;
						c2 = ch;
					}
					ch = scanner.skipWhite(ch);
				} else {
					scanner.unget_ch(ch2);
				}
			}
//			int p_start = scanner.getOffset()-1;
			
			if (ch == -1) {
				break;
			}
			
			scanner.unget_ch(ch);
			
			boolean param_ends_with_paren = false;
			
			// Skip an argument, including () 
			ch = scanner.get_ch();
			do {
				sb.append((char)ch);
				param_ends_with_paren = false;

				if (ch == '(') {
					ch = skipPastMatchSkipStrings(sb, scanner, '(', ')');
					param_ends_with_paren = true;
					
//					if (fDebugEn) {
//						debug("    post-skip (): ch=" + (char)ch);
//					}
				} else if (ch == '{') {
					ch = skipPastMatchSkipStrings(sb, scanner, '{', '}');
//					if (fDebugEn) {
//						debug("    post-skip {}: ch=" + (char)ch);
//					}
				} else if (ch == '"') {
					while ((ch = scanner.get_ch()) != -1 && 
							ch != '"' && ch != '\n') {
						sb.append((char)ch);
					}
					if (ch == '"') {
						sb.append((char)ch);
						ch = scanner.get_ch();
					}
				} else {
					ch = scanner.get_ch();
				}
			} while (ch != -1 && ch != ',' && ch != ')');
			
//			int p_end = scanner.getOffset();
			
			// Skip over the parameter-separator or the closing paren
			if (ch == ',' || ch == ')') {
				if ((!param_ends_with_paren && sb.charAt(sb.length()-1) == ')') ||
						sb.charAt(sb.length()-1) == ',') {
					sb.setLength(sb.length()-1); // trim closing ')'
				}
				if (params.size() > idx) {
					params.set(idx, sb.toString().trim());
				} else {
					params.add(sb.toString().trim());
				}
				if(ch == ')') {
					//Last parameter parsed
					ch = scanner.get_ch();
					break;
				}
				ch = scanner.get_ch();
			} else {
				if (params.size() > idx) {
					params.set(idx, sb.toString().trim());
				} else {
					params.add(sb.toString().trim());
				}
			}
			idx++;
		}
		
		scanner.unget_ch(ch);
		
//		if (fDebugEn) {
//			for (String s : params) {
//				debug("Param: \"" + s + "\"");
//			}
//			debug("<-- parse_params(" + m.getName() + ") => " + params.size() +
//					" trailing ch=" + (char)ch);
//		}
	}

	/**
	 * Expand parameter references by name in the identified 
	 * text block
	 * 
	 * @param scanner
	 * @param param_names
	 * @param param_vals
	 */
	private void expandParameterRefs(
			ITextScanner				scanner,
			StringBuilder				out,
			List<String>				param_names,
			List<String>				param_vals) {
		int ch;
		StringBuilder sb = new StringBuilder();

//		if (fDebugEn) {
//			debug("--> expandParameterRefs");
//			
//			for (int i=0; i<param_names.size(); i++) {
//				debug("Param[" + i + "] " + param_names.get(i) + " = " +
//						param_vals.get(i));
//			}
//			
//			debug("pre=" + scanner.getStorage());
//			
//			debug("offset=" + (char)scanner.charAt(scanner.getOffset()) + 
//					" limit=" + (char)scanner.charAt(scanner.getLimit()-1));
//		}

		// Read individual identifiers. Ignore un-escaped strings
		int last_ch = -1;
		while ((ch = scanner.get_ch()) != -1) {
			if (fDebugChEn) {
				debug("  ch=" + (char)ch + " last_ch=" + (char)last_ch);
			}
			if (ch == '"' && last_ch != '`') {
				// un-escaped string
				sb.append((char)ch);
				// Skip until the end of this string
				while ((ch = scanner.get_ch()) != -1 && ch != '"' && last_ch != '\\') {
					sb.append((char)ch);
					last_ch = ch;
				}
				scanner.unget_ch(ch);
			} else if (ch == '`' && last_ch == '`') {
				// Handle `` as a token separator
				if (fDebugEn) {
					debug("replace ``");
				}
				out.setLength(out.length()-1); // delete the extra '`'
			} else if (Character.isJavaIdentifierStart(ch)) {
//				int p_start = scanner.getOffset()-1;
//				int p_end;

				sb.setLength(0);
				ch = AbstractTextScanner.readPreProcIdentifier(sb, scanner, ch);
				last_ch = ch;
				scanner.unget_ch(ch);
				
				String key = sb.toString();

//				if (fDebugEn) {
//					debug("offset=" + scanner.getOffset() + " limit=" + scanner.getLimit());
//				}
//				p_end = scanner.getOffset();

				int index = param_names.indexOf(key);
				if (index != -1 && index < param_vals.size()) {
//					if (fDebugEn) {
//						debug("Replacing parameter \"" + key + "\" with \"" +
//								param_vals.get(index) + "\"");
//						debug("start_p=" + p_start + " end_p=" + p_end + " offset-1=" + (scanner.getOffset()-1));
//					}
					out.append(param_vals.get(index));
//					scanner.replace(p_start, p_end, param_vals.get(index));
				} else {
					out.append(key);
				}
			} else {
				sb.append((char)ch);
				last_ch = ch;
			}
		}

//		if (fDebugEn) {
//			debug("post=" + scanner.getStorage());
//			debug("<-- expandParameterRefs");
//		}
	}
	
	private void debug(String str) {
		if (fDebugEn) {
			fLog.debug(str);
		}
	}

	private String readLine(ITextScanner scanner, int ci) {
		StringBuilder buffer = new StringBuilder();
		int last_ch = -1;
		
		buffer.setLength(0);
		while (ci != -1 && ci != '\n' || last_ch == '\\') {
			if (last_ch == '\\' && ci == '\n') {
				if (buffer.charAt(buffer.length()-1) == '\r') {
					buffer.setLength(buffer.length()-1);
				}
				if (buffer.charAt(buffer.length()-1) == '\\') {
					buffer.setCharAt(buffer.length()-1, '\n');
				}
			} else {
				buffer.append((char)ci);
			}

			if (ci != '\r') {
				last_ch = ci;
			}

			ci = scanner.get_ch();
		}
		
		scanner.unget_ch(ci);

		if (buffer.length() == 0) {
			return null;
		} else {
			return buffer.toString();
		}
	}	
	
	private void push_input(Input in) {
		fInputStack.push(in);
		fInputCurr = in;
	}
	
	public int get_ch() {
		int ret;
		while ((ret = fInputCurr.fScanner.get_ch()) == -1) {
			if (fInputStack.size() > 0) {
				fInputStack.pop();
				fInputCurr = fInputStack.peek();
			} else {
				break;
			}
		}
		return ret;
	}
	
	public void unget_ch(int ch) {
		fInputCurr.fScanner.unget_ch(ch);
	}

	@Override
	public long getPos() {
		return 0;
	}

	private void output(String str) {
		fOutput.append(str);
	}
	
	private void output(char ch) {
		fOutput.append(ch);
	}
	
	private boolean ifdef_enabled() {
		
		if (fPreProcEn.size() == 0) {
			return true;
		} else {
			int e = fPreProcEn.peek();
			return ((e & PP_ENABLED) == PP_ENABLED);
		}
	}
	
	private void enter_ifdef(long scan_loc, boolean enabled) {
		boolean enabled_pre = ifdef_enabled();
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
//		fPreProcLoc.push(scan_loc);
	
		if (fDebugEn) {
			fLog.debug("enter_ifdef: " + SVDBLocation.unpackLineno(scan_loc) + 
					" enabled=" + enabled + " pre=" + enabled_pre + 
					" post=" + ifdef_enabled() + " sz=" + fPreProcEn.size());
		}
		
//		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void leave_ifdef(long scan_loc) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			fPreProcEn.pop();
//			fPreProcLoc.pop();
		}
	
		if (fDebugEn) {
			fLog.debug("leave_ifdef: " + SVDBLocation.unpackLineno(scan_loc) + 
					" pre=" + enabled_pre + 
					" post=" + ifdef_enabled());
		}
		
//		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void enter_elsif(long scan_loc, boolean enabled) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();
//			fPreProcLoc.pop();

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
//			fPreProcLoc.push(scan_loc);
		}
//		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void enter_else(long scan_loc) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();
//			fPreProcLoc.pop();
			
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
//			fPreProcLoc.push(scan_loc);
		} else {
			fLog.debug("Warning: encountered `else with empty PreProcEn stack");
		}
		
		if (fDebugEn) {
			fLog.debug("enter_else: " + SVDBLocation.unpackLineno(scan_loc) + 
					" pre=" + enabled_pre + 
					" post=" + ifdef_enabled());
		}
		
//		update_unprocessed_region(scan_loc, enabled_pre);
	}

}

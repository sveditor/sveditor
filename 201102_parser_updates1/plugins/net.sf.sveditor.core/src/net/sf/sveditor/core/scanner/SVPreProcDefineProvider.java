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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.utils.SVDBItemPrint;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class SVPreProcDefineProvider implements IDefineProvider {
	private static final boolean		fDebugEn				= false;
	private static final boolean		fDebugChEn				= false;
	private boolean						fDebugUndefinedMacros	= false;
	private String						fFilename;
	private int							fLineno;
	private Stack<String>				fExpandStack;
	private Stack<Boolean>				fEnableOutputStack;
	private LogHandle					fLog;
	private IPreProcMacroProvider		fMacroProvider;
	private List<IPreProcErrorListener>	fErrorListeners;

	public SVPreProcDefineProvider(IPreProcMacroProvider macro_provider) {
		fExpandStack = new Stack<String>();
		fEnableOutputStack = new Stack<Boolean>();
		fLog = LogFactory.getLogHandle("PreProcDefineProvider");

		fMacroProvider  = macro_provider;
		fErrorListeners = new ArrayList<IPreProcErrorListener>();
	}
	
	public void addErrorListener(IPreProcErrorListener l) {
		fErrorListeners.add(l);
	}

	public void removeErrorListener(IPreProcErrorListener l) {
		fErrorListeners.remove(l);
	}
	
	public void error(String msg, String filename, int lineno) {
		for (IPreProcErrorListener l : fErrorListeners) {
			l.preProcError(msg, filename, lineno);
		}
	}

	public void setMacroProvider(IPreProcMacroProvider provider) {
		fMacroProvider = provider;
	}
	
	public IPreProcMacroProvider getMacroProvider() {
		return fMacroProvider;
	}
	
	public void addDefines(Map<String, String> defs) {
		for (String key : defs.keySet()) {
			fMacroProvider.setMacro(key, defs.get(key));
		}
	}
	
	public boolean isDefined(String name, int lineno) {
		SVDBMacroDef m = fMacroProvider.findMacro(name, lineno);
		
		// The location is null for command-line defines
		if (m != null) {
			return (m.getLocation() == null || m.getLocation().getLine() <= lineno);
		} else {
			return false;
		}
	}

	public synchronized String expandMacro(
			String 			str, 
			String 			filename, 
			int 			lineno) {
		StringTextScanner scanner = new StringTextScanner(
				new StringBuilder(str));
		
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
		fExpandStack.clear();
		fEnableOutputStack.clear();
		fEnableOutputStack.push(true);

		expandMacro(scanner);
		
		if (fDebugEn) {
			debug("<-- expandMacro(str): " + str);
			debug("    Result: " + scanner.getStorage().toString());
		}
		
		return scanner.getStorage().toString();
	}

	/**
	 * Expand the text in 'scanner', inserting the new text into
	 * the scanner storage buffer
	 * 
	 * @param scanner
	 * @return
	 */
	private int expandMacro(StringTextScanner scanner) {
		if (fDebugEn) {
			debug("--> expandMacro(scanner)");
		}
		int macro_start = scanner.getOffset();

		int ch = scanner.get_ch();
		
		// Expect this to be '`'
		if (ch != '`') {
			System.out.println("[ERROR] Expect macro to start " +
					"with '`', not \"" + (char)ch + "\" @ " +
					fFilename + ":" + fLineno);
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		// Read the macro name
		String key = scanner.readPreProcIdentifier(scanner.get_ch());
		
		if (key == null) {
			ch = scanner.get_ch();
			fLog.error("Failed to read macro name starting with " + (char)ch);
			scanner.unget_ch(ch);
		} else if (key.equals("ifdef") || key.equals("ifndef") || key.equals("else") || key.equals("endif")) {
			// Don't expand
		} else {
			fExpandStack.push(key);
			
			ch = scanner.skipWhite(scanner.get_ch());
			
			SVDBMacroDef m = fMacroProvider.findMacro(key, fLineno);
			
			if (m == null) {
				error("macro \"" + key + "\" undefined");
				if (fDebugUndefinedMacros) {
					fLog.error("macro \"" + key + "\" undefined @ " +
							fFilename + ":" + fLineno);
				}
				
				/*
				if (fDebugUndefinedMacros) {
					fLog.debug("macro \"" + key + "\" undefined @ " +
							fFilename + ":" + fLineno);
					walkStack();
					boolean tmp = fDebugEnS;
					fDebugEnS = true;
					fIndent = 0;
					if (fContext != null) {
						searchContext(fContext, key);
					}
					fDebugEnS = tmp;
				}
				 */

				if (ch == '(') {
					ch = scanner.skipPastMatch("()");
					scanner.unget_ch(ch);
				}
				
				// TODO: ?
				return 0;
			}
			List<String> params = null;
			
			// If the macro has parameters, scan them now
			if (ch == '(') {
				// Before parsing the parameters, make all macro substitutions
				StringTextScanner scanner_s;

				if (fDebugEn) {
					debug("pre-expand: str=" + scanner.getStorage());
				}
				expandMacroRefs(new StringTextScanner(scanner, scanner.getOffset()));
				if (fDebugEn) {
					debug("post-expand: str=" + scanner.getStorage());
				}
				
				params = parse_params(m, scanner);
				
				scanner_s = new StringTextScanner(scanner, 
						macro_start, scanner.getOffset());
				expandMacro(scanner_s, m, params);
				
				if (fDebugEn) {
					debug("Expansion of " + m.getName() + " is: " +
							scanner.getStorage().toString());
				}
				
				ch = scanner.get_ch();

			} else {
				// Simple -- just replace the text range with the macro text
				StringTextScanner scanner_s = new StringTextScanner(
						scanner, macro_start, scanner.getOffset());
				
				expandMacro(scanner_s, m, null);
				
				scanner.seek(scanner_s.getOffset()-1);
				
				if (fDebugEn) {
					debug("Expansion Result: " + scanner_s.getStorage().toString());
				}
				/*
				scanner.replace(macro_start, scanner.getOffset(), 
						scanner_s.getStorage().toString());
				 */
			}
			fExpandStack.pop();
			if (fDebugEn) {
				debug("<-- expandMacro(scanner)");
			}
		}
		
		return 0;
	}

	/****************************************************************
	 * expandMacro()
	 *
	 * Pre-conditions:  scanner from getOffset to getLimit is the
	 *                  macro to expand
	 *                  
	 *                  At this point, no macro parameters have been
	 *                  expanded. Macro calls within the macro definition
	 *                  body are also still unexpanded.
	 *                 
	 * Post-conditions: 
	 ****************************************************************/
	private void expandMacro(
			StringTextScanner		scanner,
			SVDBMacroDef 			m, 
			List<String> 			params) {
		boolean expand_params = (params != null);
		if (fDebugEn) {
			debug("--> expandMacro(" + m.getName() + ")");
			debug("    text=" + scanner.substring(scanner.getOffset(), scanner.getLimit()));
		}
		
		if (expand_params) {
			expand_params = (params.size() == m.getParameters().size());
			if (params.size() != m.getParameters().size()) {
				System.out.println("[ERROR] param count for macro \"" + 
						m.getName() + "\" doesn't match: " + 
						params.size() + " vs " + m.getParameters().size());
				System.out.println("    Location: " + fFilename + ":" + fLineno);
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
		
		if (m.getDef() == null) {
			System.out.println("[ERROR] macro definition for key \"" + 
					m.getName() + "\" is null");
			ISVDBChildItem top = m;
			
			while (top.getParent() != null) {
				top = top.getParent();
			}
			System.out.println("Dumping null-macro provider");
			SVDBItemPrint.printItem(top);
			walkStack();
		}
		
		if (fDebugEn) {
			debug("def=" + m.getDef());
		}
		
		if (m.getDef() == null) {
			System.out.println("Macro \"" + m.getName() + "\" @ <<UNKNOWN>>:" + 
					m.getLocation().getLine() + " is null");
			// Replace the text with ""
			scanner.replace(scanner.getOffset(), scanner.getLimit(), "");
		} else {
			// Replace the text and adjust the limits
			scanner.replace(scanner.getOffset(), scanner.getLimit(), m.getDef());
		}

		// Expand the parameter references within the replacement
		if (expand_params) {
			expandParameterRefs(new StringTextScanner(scanner), 
					m.getParameters(), params);
		}

		// Expand pre-processor references within the replacement
		expandMacroRefs(new StringTextScanner(scanner));
		
		if (fDebugEn) {
			debug("    text=" + scanner.getStorage().toString());
			debug("<-- expandMacro(" + m.getName() + ")");
		}
	}
	
	private List<String> parse_params(
			SVDBMacroDef			m,
			StringTextScanner 		scanner) {
		if (fDebugEn) {
			debug("--> parse_params(" + m.getName() + ")");
			debug("    str=" + scanner.getStorage().substring(scanner.getOffset()));
		}
		List<String> params = new ArrayList<String>();
		int ch = scanner.get_ch();
		
		for (int i=0; i<m.getParameters().size(); i++) {
			ch = scanner.skipWhite(ch);
			int p_start = scanner.getOffset()-1;
			
			if (ch == -1) {
				break;
			}
			
			scanner.unget_ch(ch);
			
			// Skip an argument, including () 
			do {
				ch = scanner.get_ch();

				if (ch == '(') {
					ch = scanner.skipPastMatch("()");
					
					if (fDebugEn) {
						debug("    post-skip (): ch=" + (char)ch);
					}
				} else if (ch == '{') {
					ch = scanner.skipPastMatch("{}");
					if (fDebugEn) {
						debug("    post-skip {}: ch=" + (char)ch);
					}
				}
			} while (ch != -1 && ch != ',' && ch != ')');
			
			int p_end = scanner.getOffset();
			
			String param;
			
			if (scanner.getStorage().charAt(p_start) == '`') {
				// Need to sub-expand this parameter
				StringTextScanner scanner_s = new StringTextScanner(
						new StringBuilder(scanner.substring(p_start, p_end-1)));
				if (fDebugEn) {
					debug("String passed to expandMacro(1): \"" + 
							scanner.substring(p_start, p_end-1) + "\"");
					/*
					debug("First char=" + (char)scanner_s.get_ch());
					debug("Second char=" + (char)scanner_s.get_ch());
					 */
				}
				
				if (Character.isJavaIdentifierStart(scanner.getStorage().charAt(p_start+1))) {
					expandMacro(scanner_s);
				} else {
					// TODO: probably a string
					while ((ch = scanner_s.get_ch()) != -1) {
						if (ch == '`') {
							int ch2 = scanner_s.get_ch();
							
							if (ch2 == '`') {
								scanner_s.delete(scanner_s.getOffset()-2, scanner_s.getOffset());
							} else {
								scanner_s.delete(scanner_s.getOffset()-2, scanner_s.getOffset()-1);
							}
						}
					}
				}

				param = scanner_s.getStorage().toString();
				
				if (fDebugEn) {
					debug("Parameter (with params): " + param);
				}
			} else {
				param = scanner.getStorage().substring(p_start, p_end-1);
				
				if (fDebugEn) {
					debug("Parameter (no params): " + param);
				}
			}
			
			params.add(param.trim());
			
			// Skip over the parameter-separator or the closing paren
			debug("    Try Skip: next ch=" + (char)ch);
			if (ch == ',' || ch == ')') {
				ch = scanner.get_ch();
			}
		}
		
		scanner.unget_ch(ch);
		
		if (fDebugEn) {
			for (String s : params) {
				debug("Param: \"" + s + "\"");
			}
			debug("<-- parse_params(" + m.getName() + ") => " + params.size() +
					" trailing ch=" + (char)ch);
		}
		
		return params;
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
			StringTextScanner			scanner,
			List<String>				param_names,
			List<String>				param_vals) {
		int ch;

		if (fDebugEn) {
			for (int i=0; i<param_names.size(); i++) {
				debug("Param[" + i + "] " + param_names.get(i) + " = " +
						param_vals.get(i));
			}
			
			debug("--> expandParameterRefs");
			debug("pre=" + scanner.getStorage());
		}

		// Read individual identifiers. Ignore un-escaped strings
		int last_ch = -1;
		while ((ch = scanner.get_ch()) != -1) {
			if (ch == '"' && last_ch != '`') {
				// un-escaped string
				while ((ch = scanner.get_ch()) != -1 && ch != '"') { }
			} else if (Character.isJavaIdentifierStart(ch)) {
				int p_start = scanner.getOffset()-1;
				
				String key = scanner.readPreProcIdentifier(ch);

				int index = param_names.indexOf(key);
				if (index != -1 && index < param_vals.size()) {
					if (fDebugEn) {
						debug("Replacing parameter \"" + key + "\" with \"" +
								param_vals.get(index) + "\"");
					}
					scanner.replace(p_start, scanner.getOffset()-1, 
							param_vals.get(index));
				}
			}
			
			last_ch = ch;
		}

		if (fDebugEn) {
			debug("<-- expandParameterRefs");
			debug("post=" + scanner.getStorage());
		}
	}
	
	private void expandMacroRefs(StringTextScanner scanner) {
		int ch;
		int iteration = 0;
		int marker = -1;
		
		if (fDebugEn) {
			debug("--> expandMacroRefs");
			debug("pre=" + scanner.getStorage().substring(scanner.getOffset(), scanner.getLimit()));
		}
		
		while ((ch = scanner.get_ch()) != -1) {
			iteration++;
			
			if (fDebugChEn) {
				debug("ch=\"" + (char)ch + "\"");
			}
			if (ch == '`') {
				int macro_start = scanner.getOffset()-1;
				int ch2 = scanner.get_ch();
				if (fDebugChEn) {
					debug("    ch2=\"" + (char)ch2 + "\"");
				}
				if (ch2 == '`') {
					// Nothing -- `` is the same as ## in C++ pre-proc
					scanner.delete(scanner.getOffset()-2, scanner.getOffset());
					debug("        delete ``");
				} else if (ch2 == '"' || ch2 == '\\') {
					scanner.delete(scanner.getOffset()-2, scanner.getOffset()-1);
				} else {
					
					// Expect an identifier
					int m_start = scanner.getOffset()-2;
					
					ch = scanner.skipWhite(ch2);

					// Skip any non-identifier characters
					// TODO: this seems a bit strange...
					if (!SVCharacter.isSVIdentifierStart(ch)) {
						continue;
					}
					
					String key = scanner.readPreProcIdentifier(ch);
					
					if (key == null) {
						fLog.error("Failed to read macro name starting with " +	(char)ch);
					}
					
					// Handle macro-embedded pre-processor directives
					if (key.equals("ifdef") || key.equals("ifndef")) {
						ch = scanner.skipWhite(scanner.get_ch());
						String condition = scanner.readPreProcIdentifier(ch);
						SVDBMacroDef cond_m = fMacroProvider.findMacro(condition, fLineno);
						// delete the ifdef/ifndef statement
						scanner.delete(macro_start, scanner.getOffset());
						boolean en = (fEnableOutputStack.peek() &&
								((key.equals("ifdef") && cond_m != null) ||
										(key.equals("ifndef") && cond_m == null)));

						// Mark the beginning of a section of text to delete
						if (fEnableOutputStack.peek() && !en) {
							marker = scanner.getOffset();
						}
						fEnableOutputStack.push(en);
					} else if (key.equals("undef")) {
						ch = scanner.skipWhite(scanner.get_ch());
						/*String macro = */scanner.readPreProcIdentifier(ch);

						// delete the undef statement
						scanner.delete(macro_start, scanner.getOffset());
					} else if (key.equals("else")) {
						scanner.delete(macro_start, scanner.getOffset());
						if (fEnableOutputStack.size() > 1) {
							boolean en = fEnableOutputStack.pop();
							
							// Delete the portion of text
							if (marker != -1 && !en && fEnableOutputStack.peek()) {
								scanner.delete(marker, scanner.getOffset());
								marker = -1;
							} else if (marker == -1 && en && fEnableOutputStack.peek()) {
								// We're transitioning into a disabled portion
								marker = scanner.getOffset();
							}
							fEnableOutputStack.push(!en);
						}
					} else if (key.equals("endif")) {
						scanner.delete(macro_start, scanner.getOffset());
						if (fEnableOutputStack.size() > 1) {
							boolean en = fEnableOutputStack.pop();
							if (marker != -1 && !en && fEnableOutputStack.peek()) {
								scanner.delete(marker, scanner.getOffset());
								marker = -1;
							}
						}
					} else {
						SVDBMacroDef sub_m = fMacroProvider.findMacro(key, fLineno);
						List<String> sub_p = null;
						ch = scanner.get_ch();
						
						if (fDebugEn) {
							debug("    ref=\"" + key + "\"");
						}
						
						int m_end = scanner.getOffset();
						
						if (hasParameters(key, fLineno)) {
							// TODO: Need to expand parameter references in this macro call
							
							if (fDebugEn) {
								debug("    \"" + key + "\" has parameters");
							}
							ch = scanner.skipWhite(ch);
							
							if (ch == '(') {
								// expand macros in parameter list
								if (fDebugEn) {
									debug("    calling expandMacroRefs: \"" + scanner.getStorage().substring(scanner.getOffset()) + "\"");
								}
								expandMacroRefs(new StringTextScanner(scanner, scanner.getOffset()));
								sub_p = parse_params(sub_m, scanner);
								ch = scanner.get_ch();
							}
							m_end = scanner.getOffset();
						} else {
							debug("    \"" + key + "\" doesn't have parameters");
						}
						
						// Now, expand this macro
						if (fDebugEn) {
							debug("post-param parse: ch=" + (char)ch);
						}
						if (ch != -1) {
							// Back up if we didn't end by exhausing the buffer. 
							// We don't want to replace the character following the macro
							scanner.unget_ch(ch);
							m_end--;
						} 
						
						if ((m_end-1) >= scanner.getStorage().length()) {
							System.out.println("m_end=" + m_end + " storage.length=" +
									scanner.getStorage().length() + 
									" scanner.offset=" + scanner.getOffset() +
									" scanner.limit=" + scanner.getLimit());
							System.out.println("storage=" + scanner.getStorage().toString());
							System.out.println("iteration=" + iteration);
						}
						if (fDebugEn) {
							debug("    text for expansion ends with \"" + 
									scanner.getStorage().charAt(m_end-1) + "\"");
						}
						StringTextScanner scanner_s = new StringTextScanner(
								scanner, m_start, m_end);
						
						if (sub_m != null) {
							if (scanner.getOffset() > scanner.getLimit()) {
								System.out.println("scanner offset > limit before sub-expand iteration "
										+ iteration);
								System.out.println("    sub-expand of " + sub_m.getName());
							}
							expandMacro(scanner_s, sub_m, sub_p);
							
							scanner.seek(scanner_s.getOffset()-1);
							
							if (scanner.getOffset() > scanner.getLimit()) {
								System.out.println("scanner offset > limit after sub-expand iteration "
										+ iteration);
								System.out.println("    sub-expand of " + sub_m.getName());
							}
						} else {
							if (fDebugEn) {
								debug("Macro \"" + key + 
									"\" undefined @ " + fFilename + ":" + fLineno);
							}
							scanner.delete(m_start, m_end-1);
							walkStack();
						}
					}
				}
			}
		}
		
		if (fDebugEn) {
			debug("post=" + scanner.getStorage());
			debug("<-- expandMacroRefs");
		}
	}

	public boolean hasParameters(String key, int lineno) {
		
		SVDBMacroDef m = fMacroProvider.findMacro(key, lineno);
		
		if (m != null) {
			return (m.getParameters().size() != 0);
		} else {
			return false;
		}
	}
	
	private void error(String msg) {
		for (IPreProcErrorListener l : fErrorListeners) {
			l.preProcError(msg, fFilename, fLineno);
		}
	}

	private void walkStack() {
		String key;
		Stack<String> tmp = new Stack<String>();
		tmp.addAll(fExpandStack);
		
		fLog.debug("walkStack");
		while (tmp.size() > 0) {
			key = tmp.pop();
			fLog.debug("    " + key);
		}
	}
	
	private void debug(String str) {
		if (fDebugEn) {
			fLog.debug(str);
		}
	}

}

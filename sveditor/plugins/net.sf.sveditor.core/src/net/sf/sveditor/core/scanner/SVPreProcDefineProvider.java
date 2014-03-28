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


package net.sf.sveditor.core.scanner;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.utils.SVDBItemPrint;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.ITextScanner;
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
		fLog = LogFactory.getLogHandle("SVPreProcDefineProvider");

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
		
		/*
		return (m != null);
		 */
	
		// The location is null for command-line defines
		if (m != null) {
			// TODO: unsure 
			if (lineno == -1) {
				return true;
			} else {
				return (m.getLocation() == null || m.getLocation().getLine() <= lineno);
			}
//			return true;
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
		
		if (fDebugEn) {
			debug("  key=\"" + key + "\"");
		}
		
		if (key == null) {
			ch = scanner.get_ch();
			error("Failed to read macro name starting with " + (char)ch);
			scanner.unget_ch(ch);
		} else if (key.equals("ifdef") || key.equals("ifndef") || key.equals("else") || key.equals("endif")) {
			// Don't expand
		} else {
			fExpandStack.push(key);
			
			ch = scanner.skipWhite(scanner.get_ch());
			
			SVDBMacroDef m = fMacroProvider.findMacro(key, fLineno);
			Set<String> referenced_macros = new HashSet<String>();
			
			if (m == null) {
				error("macro \"" + key + "\" undefined");
				if (fDebugUndefinedMacros) {
					fLog.error("macro \"" + key + "\" undefined @ " +
							fFilename + ":" + fLineno);
				}
				
				if (ch == '(') {
					ch = skipPastMatchSkipStrings(scanner, '(', ')');
					scanner.unget_ch(ch);
				}
				
				// TODO: replace text with appropriate number of new-line characters?
				int newline_count = 0;
				for (int i=macro_start; i<scanner.getOffset(); i++) {
					if (scanner.charAt(i) == '\n') {
						newline_count++;
					}
				}
				if (newline_count > 0) {
					StringBuilder replace = new StringBuilder();
					while (newline_count > 0) {
						replace.append("\n");
						newline_count--;
					}
					scanner.replace(macro_start, scanner.getOffset(), replace.toString());
				} else {
					// Replace text of the undefined macro with whitespace
					scanner.replace(macro_start, scanner.getOffset(), "");
				}
				
				// TODO: ?
				return 0;
			}
			List<String> params = null;
			
			// If the macro has parameters, scan them now
			if (ch == '(') {
				// Before parsing the parameters, make all macro substitutions
				StringTextScanner scanner_s;

				
				scanner_s = new StringTextScanner(scanner, scanner.getOffset());
				
				if (fDebugEn) {
					debug("pre-expand: str=" + scanner.getStorage());
					debug("  start=" + (char)scanner_s.charAt(scanner_s.getOffset()));
				}
				
				expandMacroRefs(scanner_s, referenced_macros);
				
				if (fDebugEn) {
					debug("post-expand: str=" + scanner.getStorage());
				}
				
				params = parse_params(m, scanner);
				
				scanner_s = new StringTextScanner(scanner, 
						macro_start, scanner.getOffset());
				expandMacro(scanner_s, m, params, referenced_macros);
				
				if (fDebugEn) {
					debug("Expansion of " + m.getName() + " is: " +
							scanner.getStorage().toString());
				}
				
				ch = scanner.get_ch();

			} else {
				// Simple -- just replace the text range with the macro text
				StringTextScanner scanner_s = new StringTextScanner(
						scanner, macro_start, scanner.getOffset());
				
				if (fDebugEn) {
					debug("Replacing \"" + 
							(char)scanner_s.charAt(scanner_s.getOffset()) + "\" .. \"" +
							(char)scanner_s.charAt(scanner_s.getLimit()-1) + "\"");
				}
				
				expandMacro(scanner_s, m, null, referenced_macros);
				
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
	
	private int skipPastMatchSkipStrings(ITextScanner scanner, int ch1, int ch2) {
		int ch;
		int lcnt=1, rcnt=0;
		
		while ((ch = scanner.get_ch()) != -1) {
			if (ch == ch1) {
				lcnt++;
			} else if (ch == ch2) {
				rcnt++;
			} else if (ch == '"') {
				skipPastString(scanner);
			}
			if (lcnt == rcnt) {
				break;
			}
		}
		
		return scanner.get_ch();
	}
	
	private void skipPastString(ITextScanner scanner) {
		int ch;
		int last_ch = -1;
		
		while ((ch = scanner.get_ch()) != -1) {
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
			List<String> 			params_vals,
			Set<String>				referenced_params) {
		boolean expand_params = (params_vals != null);
		List<String> param_names = new ArrayList<String>();
		
		if (fDebugEn) {
			debug("--> expandMacro(" + m.getName() + ")");
			debug("    text=" + scanner.substring(scanner.getOffset(), scanner.getLimit()));
		}
		
		// Iterate through the specified and definition arguments,
		// potentially adding default values
		if (m.getParameters() != null) {
			for (int i=0; i<m.getParameters().size(); i++) {
				SVDBMacroDefParam mp = m.getParameters().get(i);
				param_names.add(mp.getName());
				if ((params_vals == null || i >= params_vals.size()) && mp.getValue() != null) {
					if (fDebugEn) {
						debug("Using default value \"" + mp.getValue() + 
								"\" for parameter " + mp.getName());
					}
					params_vals.add(mp.getValue());
				}
			}
		}

		if (expand_params) {
			expand_params = (params_vals.size() == param_names.size());
			if (params_vals.size() != param_names.size()) {
				error("param count for macro \"" + 
						m.getName() + "\" doesn't match: " + 
						params_vals.size() + " vs " + m.getParameters().size());
//				fLog.error("    Location: " + fFilename + ":" + fLineno);
				if (fDebugEn) {
					try {
						throw new Exception();
					} catch (Exception e) {
						fLog.debug("Location of mismatch", e);
					}
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
			int start = scanner.getOffset();
			int limit = scanner.getLimit();

			scanner.replace(start, limit, m.getDef());
			if (fDebugEn) {
				debug("  existing: " + (limit-start) + " new: " + m.getDef().length());
			}
		}

		// Expand the parameter references within the replacement
		if (expand_params) {
			StringTextScanner scanner_p = new StringTextScanner(scanner);
			expandParameterRefs(scanner_p, param_names, params_vals);
		}

		// Expand pre-processor references within the replacement
		if (!referenced_params.contains(m.getName())){ 
			referenced_params.add(m.getName());
			StringTextScanner scanner_p = new StringTextScanner(scanner);
			
			if (fDebugEn) {
				debug("  pre-expandMacroRefs: \"" + 
					(char)scanner_p.charAt(scanner_p.getOffset()) + "\" \"" +
					(char)scanner_p.charAt(scanner_p.getLimit()-1) + "\"");
			}
			
			expandMacroRefs(scanner_p, referenced_params);
			referenced_params.remove(m.getName());
		} else {
			// TODO:
		}
		
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
			
			if (ch == '/') {
				int ch2 = scanner.get_ch();
				System.out.println("ch=" + (char)ch + " ch2=" + (char)ch2);
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
			int p_start = scanner.getOffset()-1;
			
			if (ch == -1) {
				break;
			}
			
			scanner.unget_ch(ch);
			
			// Skip an argument, including () 
			do {
				ch = scanner.get_ch();

				if (ch == '(') {
					ch = skipPastMatchSkipStrings(scanner, '(', ')');
					
					if (fDebugEn) {
						debug("    post-skip (): ch=" + (char)ch);
					}
				} else if (ch == '{') {
					ch = skipPastMatchSkipStrings(scanner, '{', '}');
					if (fDebugEn) {
						debug("    post-skip {}: ch=" + (char)ch);
					}
				} else if (ch == '"') {
					while ((ch = scanner.get_ch()) != -1 && 
							ch != '"' && ch != '\n') {}
					if (ch == '"') {
						ch = scanner.get_ch();
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
				if(ch == ')') {
					//Last parameter parsed
					ch = scanner.get_ch();
					break;
				}
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
			debug("--> expandParameterRefs");
			
			for (int i=0; i<param_names.size(); i++) {
				debug("Param[" + i + "] " + param_names.get(i) + " = " +
						param_vals.get(i));
			}
			
			debug("pre=" + scanner.getStorage());
			
			debug("offset=" + (char)scanner.charAt(scanner.getOffset()) + 
					" limit=" + (char)scanner.charAt(scanner.getLimit()-1));
		}

		// Read individual identifiers. Ignore un-escaped strings
		int last_ch = -1;
		while ((ch = scanner.get_ch()) != -1) {
			if (fDebugChEn) {
				debug("  ch=" + (char)ch + " last_ch=" + (char)last_ch);
			}
			if (ch == '"' && last_ch != '`') {
				// un-escaped string
				while ((ch = scanner.get_ch()) != -1 && ch != '"') { }
			} else if (ch == '`' && last_ch == '`') {
				// Handle `` as a token separator
				if (fDebugEn) {
					debug("replace ``");
				}
				scanner.replace(scanner.getOffset()-2, scanner.getOffset(), "");
			} else if (Character.isJavaIdentifierStart(ch)) {
				int p_start = scanner.getOffset()-1;
				int p_end;

				String key = scanner.readPreProcIdentifier(ch);

				if (fDebugEn) {
					debug("offset=" + scanner.getOffset() + " limit=" + scanner.getLimit());
				}
				p_end = scanner.getOffset();
/*				
				if (scanner.getOffset() >= scanner.getLimit() && key.length() == 1) {
					debug("should extend to limit");
					p_end = scanner.getOffset();
//					p_end = scanner.getOffset()-1;
				} else {
					p_end = scanner.getOffset()-1;
				}
 */				

				int index = param_names.indexOf(key);
				if (index != -1 && index < param_vals.size()) {
					if (fDebugEn) {
						debug("Replacing parameter \"" + key + "\" with \"" +
								param_vals.get(index) + "\"");
						debug("start_p=" + p_start + " end_p=" + p_end + " offset-1=" + (scanner.getOffset()-1));
					}
					scanner.replace(p_start, p_end, param_vals.get(index));
				}
			}
			
			last_ch = ch;
		}

		if (fDebugEn) {
			debug("post=" + scanner.getStorage());
			debug("<-- expandParameterRefs");
		}
	}
	
	private void expandMacroRefs(StringTextScanner scanner, Set<String> referenced_params) {
		int ch, last_ch=-1;
		int iteration = 0;
		int marker = -1;
		boolean in_string = false;
		
		if (fDebugEn) {
			debug("--> expandMacroRefs");
			debug("pre=" + scanner.getStorage().substring(scanner.getOffset(), scanner.getLimit()));
		}

		while ((ch = scanner.get_ch()) != -1) {
			iteration++;
			
			if (fDebugChEn) {
				debug("current: \"" + scanner.getStorage().toString() + "\"");
				debug("ch=\"" + (char)ch + "\" iteration=" + iteration + " " + scanner.getOffset());
			}

			if (!in_string && ch == '`') {
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
//					int m_start = scanner.getOffset()-1;

					ch = scanner.skipWhite(ch2);

					// Skip any non-identifier characters
					// TODO: this seems a bit strange...
					if (!SVCharacter.isSVIdentifierStart(ch)) {
						last_ch = ch;
						continue;
					}
					
					String key = scanner.readPreProcIdentifier(ch);
					
					if (key == null) {
						error("Failed to read macro name starting with " +	(char)ch);
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
					} else if (key.equals("define")) {
//						SVDBMacroDef m = new SVDBMacroDef();
						// TODO: save file?

						// TODO: line numbers
						ch = scanner.skipWhite(scanner.get_ch());
						
//						m.setName(scanner.readIdentifier(ch));
						scanner.readIdentifier(ch);
						
						ch = scanner.get_ch();
						
						if (ch == '(') {
							// Has parameters
							
							do {
								ch = scanner.skipWhite(scanner.get_ch());
								
								if (!(Character.isJavaIdentifierPart(ch))) {
									break;
								} else {
									String p = scanner.readIdentifier(ch);
									String dflt = null;

									ch = scanner.skipWhite(scanner.get_ch());

									if (ch == '=') {
										// Read default value
										ch = scanner.skipWhite(scanner.get_ch());
										if (ch == '"') {
											// String
											dflt = scanner.readString(ch);
											dflt = "\"" + dflt + "\"";
										} else {
											// Read up to comma or close bracket
											scanner.startCapture(ch);
											while ((ch = scanner.get_ch()) != -1 && ch != ',' && ch != ')') { }
											scanner.unget_ch(ch);
											dflt = scanner.endCapture();
										}
									} else {
										scanner.unget_ch(ch);
									}
									
//									m.addParameter(new SVDBMacroDefParam(p, dflt));
								}
								
								ch = scanner.skipWhite(scanner.get_ch());
							} while (ch == ',');
							
							if (ch == ')') {
								ch = scanner.get_ch();
							}
						}

						// Now, read the remainder of the definition
						String define = readLine(scanner, ch);
						
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
						
//						m.setDef(define);
						
//						fMacroProvider.addMacro(m);
					} else {
						SVDBMacroDef sub_m = fMacroProvider.findMacro(key, fLineno);
						List<String> sub_p = null;
						
						if (fDebugEn) {
							debug("    ref=\"" + key + "\"");
						}
						
						int m_end;
						
						if (hasParameters(key, fLineno)) {
							// TODO: Need to expand parameter references in this macro call
							
							if (fDebugEn) {
								debug("    \"" + key + "\" has parameters");
							}
							ch = scanner.skipWhite(scanner.get_ch());
							
							if (ch == '(') {
								// expand macros in parameter list
								if (fDebugEn) {
									debug("    calling expandMacroRefs: \"" + scanner.getStorage().substring(scanner.getOffset()) + "\"");
								}
								expandMacroRefs(new StringTextScanner(scanner, scanner.getOffset()), referenced_params);
								sub_p = parse_params(sub_m, scanner);
								ch = scanner.get_ch();
							}
							if (ch != -1) {
								// Back up if we didn't end by exhausing the buffer. 
								// We don't want to replace the character following the macro
								scanner.unget_ch(ch);
							}
							m_end = scanner.getOffset();
						} else {
							debug("    \"" + key + "\" doesn't have parameters");
							m_end = scanner.getOffset();
						}
						
						// Now, expand this macro
						if (fDebugEn) {
							debug("post-param parse: ch=" + (char)ch);
						}
					
						// This is an unexpected 
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
							if (!referenced_params.contains(key)) {
								referenced_params.add(key);
								// This is unexpected
								if (scanner.getOffset() > scanner.getLimit()) {
									System.out.println("scanner offset > limit before sub-expand iteration "
											+ iteration);
									System.out.println("    sub-expand of " + sub_m.getName());
								}
								expandMacro(scanner_s, sub_m, sub_p, referenced_params);
								referenced_params.remove(key);

								scanner.seek(scanner_s.getOffset());

								// This is unexpected
								if (scanner.getOffset() > scanner.getLimit()) {
									System.out.println("scanner offset > limit after sub-expand iteration "
											+ iteration);
									System.out.println("    sub-expand of " + sub_m.getName());
								}
							} else {
								if (fDebugEn) {
									debug("Macro \"" + key + "\" being recursively referenced");
								}
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
			} else if (ch == '"' && last_ch != '\\') {
				in_string = !in_string;
			}
			
			if (fDebugChEn) {
				debug("end iteration: ch=\"" + (char)ch + "\" iteration=" + iteration + " " + scanner.getOffset());
			}
			last_ch = ch;
		}
		
		if (fDebugEn) {
			debug("post=" + scanner.getStorage());
			debug("<-- expandMacroRefs");
		}
	}

	public boolean hasParameters(String key, int lineno) {
		
		SVDBMacroDef m = fMacroProvider.findMacro(key, lineno);
		
		if (m != null) {
			return (m.getParameters() != null &&
					m.getParameters().size() != 0);
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
}

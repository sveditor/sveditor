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

import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class SVSingleLevelMacroExpander {
	
	private static final boolean		fDebugEn				= false;
	private static final boolean		fDebugChEn				= false;
	private LogHandle					fLog;
	private StringBuilder				fOutput;

	public SVSingleLevelMacroExpander() {
		fLog = LogFactory.getLogHandle("SVSingleLevelMacroExpander");

		fOutput = new StringBuilder();
	}
	
	public String expandMacro(
			SVDBMacroDef	m,
			List<String>	params) {
		fOutput.setLength(0);

		if (m.getParameters() != null && m.getParameters().size() > 0) {
			List<String> param_names = new ArrayList<String>();
			for (SVDBMacroDefParam p : m.getParameters()) {
				param_names.add(p.getName());
			}
			
			expandParameterRefs(new StringTextScanner(m.getDef()), 
					fOutput, param_names, params);
		} else {
			fOutput.append(m.getDef());
		}
	
		return fOutput.toString();
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
		
		if (fDebugEn) {
			debug("expandParameterRefs: \"" + scanner.toString() + "\"");
			for (int i=0; i<param_names.size(); i++) {
				debug("  parameter name=\"" + param_names.get(i) + "\" value=\"" +
						param_vals.get(i) + "\"");
			}
		}

		// Read individual identifiers. Ignore string boundaries
		int last_ch = -1;
		while ((ch = scanner.get_ch()) != -1) {
			if (fDebugChEn) {
				debug("  ch=" + (char)ch + " last_ch=" + (char)last_ch);
			}

			if (ch == '"' && last_ch == '`') {
				// collapse to '"'
				out.setLength(out.length()-1);
				out.append((char)ch);
				last_ch = -1;
			} else if (ch == '`' && last_ch == '`') {
				// Handle `` as a token separator
				if (fDebugEn) {
					debug("replace ``");
				}
				out.setLength(out.length()-1); // delete the extra '`'
				last_ch = -1;
			} else if (Character.isJavaIdentifierStart(ch)) {
				sb.setLength(0);
				ch = AbstractTextScanner.readPreProcIdentifier(sb, scanner, ch);
				scanner.unget_ch(ch);
			
				String key = sb.toString();
				
				if (fDebugEn) {
					debug("  identifier=\"" + key + "\"");
				}

				if (param_names != null && param_vals != null &&
						param_names.size() > 0 && param_vals.size() > 0) {
					int index = param_names.indexOf(key);
					if (index != -1 && index < param_vals.size()) {
						out.append(param_vals.get(index));
					} else {
						out.append(key);
					}
				} else {
					out.append(key);
				}
				last_ch = -1;
			} else {
				out.append((char)ch);
				last_ch = ch;
			}
		}

//		if (fDebugEn) {
//			debug("post=" + scanner.getStorage());
//			debug("<-- expandParameterRefs");
//		}
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
					int last_ch = -1;
					while ((ch = scanner.get_ch()) != -1 && 
							(ch != '"' || last_ch == '\\')) {
						if (ch == '\n' && last_ch == '\\') {
							// skip both characters
							sb.setLength(sb.length()-1); // remove \n
							last_ch = -1;
						} else {
							sb.append((char)ch);
							last_ch = ch;
						}
					}
					if (ch == '"') {
						sb.append((char)ch);
						ch = scanner.get_ch();
					}
				} else if (ch != -1 && ch != ',' && ch != ')') {
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
	
	private void debug(String str) {
		if (fDebugEn) {
			fLog.debug(str);
		}
	}

}

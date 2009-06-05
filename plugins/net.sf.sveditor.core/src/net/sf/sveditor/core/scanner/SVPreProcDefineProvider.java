package net.sf.sveditor.core.scanner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemPrint;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class SVPreProcDefineProvider implements IDefineProvider {
	private SVDBFileTree				fContext;
	private boolean						fDebugEnS = false;
	private boolean						fDebugEn  = false;
	private boolean						fDebugUndefinedMacros = true;
	private String						fFilename;
	private int							fLineno;
	private Stack<String>				fExpandStack;
	private Map<String, SVDBMacroDef>	fMacroCache;
	
	
	public SVPreProcDefineProvider() {
		fExpandStack = new Stack<String>();
		fMacroCache  = new HashMap<String, SVDBMacroDef>();
	}
	
	public void setFileContext(SVDBFileTree context) {
		fContext = context;
	}
	
	public boolean isDefined(String name, int lineno) {
		SVDBMacroDef m = searchContext(fContext, name);
		
		return (m != null && m.getLocation().getLine() <= lineno);
	}

	public synchronized String expandMacro(
			String 			str, 
			String 			filename, 
			int 			lineno) {
		StringTextScanner scanner = new StringTextScanner(
				new StringBuilder(str));
		
		if (fContext == null) {
			System.out.println("[WARN] File context not set");
		}
		
		fFilename = filename;
		fLineno   = lineno;
		fExpandStack.clear();

		debug("--> expandMacro(str): " + str);

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
		debug("--> expandMacro(scanner)");
		int macro_start = scanner.getOffset();

		int ch = scanner.get_ch();
		
		// Expect this to be '`'
		if (ch != '`') {
			System.out.println("[ERROR] Expect macro to start " +
					"with '`', not " + (char)ch + " @ " +
					fFilename + ":" + fLineno);
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		// Read the macro name
		String key = scanner.readIdentifier(scanner.get_ch());
		
		if (key == null) {
			ch = scanner.get_ch();
			System.out.println("Failed to read macro name starting with " +	(char)ch);
			scanner.unget_ch(ch);
		}
		
		fExpandStack.push(key);
		
		ch = scanner.skipWhite(scanner.get_ch());
		
		SVDBMacroDef m = null;
		
		if (fContext != null) {
			m = searchContext(fContext, key);
		}
		
		if (m == null) {
			if (fDebugUndefinedMacros) {
				System.out.println("[ERROR] macro \"" + key + "\" undefined @ " +
						fFilename + ":" + fLineno);
			}
			
			if (fDebugUndefinedMacros) {
				walkStack();
				boolean tmp = fDebugEnS;
				fDebugEnS = true;
				if (fContext != null) {
					searchContext(fContext, key);
				}
				fDebugEnS = tmp;
			}

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
			
			if (fDebugEn) {
				debug("Expansion Result: " + scanner_s.getStorage().toString());
			}
			/*
			scanner.replace(macro_start, scanner.getOffset(), 
					scanner_s.getStorage().toString());
			 */
		}
		
		fExpandStack.pop();
		debug("<-- expandMacro(scanner)");
		return 0;
	}

	/****************************************************************
	 * expandMacro()
	 * 
	 ****************************************************************/
	private void expandMacro(
			StringTextScanner		scanner,
			SVDBMacroDef 			m, 
			List<String> 			params) {
		boolean expand_params = (params != null);
		debug("--> expandMacro(" + m.getName() + ")");
		if (fDebugEn) {
			if (scanner.substring(scanner.getOffset(), scanner.getLimit()).equals("`ovm_component_utils_en")) {
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
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
			SVDBItem top = m;
			
			while (top.getParent() != null) {
				top = top.getParent();
			}
			System.out.println("Dumping null-macro provider");
			SVDBItemPrint.printItem(top);
			walkStack();
		}
		
		debug("def=" + m.getDef());
		
		if (m.getDef() == null) {
			System.out.println("Macro \"" + m.getName() + "\" @ " + 
					m.getLocation().getFile().getFilePath() + ":" +
					m.getLocation().getLine() + " is null");
		}
		
		// Replace the text and adjust the limits
		scanner.replace(scanner.getOffset(), scanner.getLimit(), m.getDef());

		// Expand the parameter references within the replacement
		if (expand_params) {
			expandParameterRefs(new StringTextScanner(scanner), 
					m.getParameters(), params);
		}

		// Expand pre-processor references within the replacement
		expandMacroRefs(new StringTextScanner(scanner));
		
		
		if (fDebugEn) {
			debug("    text=" + scanner.getStorage().toString());
		}
		debug("<-- expandMacro(" + m.getName() + ")");
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
					
					debug("    post-skip (): ch=" + (char)ch);
				}
			} while (ch != -1 && ch != ',' && ch != ')');
			
			int p_end = scanner.getOffset();
			
			String param;
			if (scanner.getStorage().charAt(p_start) == '`') {
				// Need to sub-expand this parameter
				StringTextScanner scanner_s = new StringTextScanner(
						scanner, p_start, p_end-1);
				if (fDebugEn) {
					debug("String passed to expandMacro(1): " + 
							scanner_s.substring(p_start, p_end-1));
				}
				expandMacro(scanner_s);

				param = scanner_s.getStorage().toString();
			} else {
				param = scanner.getStorage().substring(p_start, p_end-1);
			}
			
			params.add(param);
			
			if (ch == ',') {
				ch = scanner.get_ch();
			}
		}
		
		if (ch != -1) {
			ch = scanner.skipWhite(ch);
		}
		
		if (fDebugEn) {
			for (String s : params) {
				debug("Param: \"" + s + "\"");
			}
		}
		
		debug("<-- parse_params(" + m.getName() + ") => " + params.size());
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
			debug("pre=" + scanner.getStorage());
		}

		while ((ch = scanner.get_ch()) != -1) {
			if (Character.isJavaIdentifierStart(ch)) {
				int p_start = scanner.getOffset()-1;
				
				String key = scanner.readIdentifier(ch);

				int index = param_names.indexOf(key);
				if (index != -1 && index < param_vals.size()) {
					debug("Replacing parameter \"" + key + "\"");
					scanner.replace(p_start, scanner.getOffset()-1, 
							param_vals.get(index));
				}
			} else if (ch == '"') {
				// Don't consider `" 
				if (scanner.getOffset() == 0 || 
						scanner.getStorage().charAt(scanner.getOffset()-1) != '`') {
					// Could skip string...
					scanner.readString(ch);
				}
			}
		}

		if (fDebugEn) {
			debug("<-- expandParameterRefs");
			debug("post=" + scanner.getStorage());
		}
	}
	
	private void expandMacroRefs(StringTextScanner scanner) {
		int ch;
		
		if (fDebugEn) {
			debug("--> expandMacroRefs");
			debug("pre=" + scanner.getStorage().substring(scanner.getOffset(), scanner.getLimit()));
		}
		
		while ((ch = scanner.get_ch()) != -1) {
			if (ch == '`') {
				int ch2 = scanner.get_ch();
				
				if (ch2 == '`') {
					// Nothing -- `` is the same as ## in C++ pre-proc
					scanner.delete(scanner.getOffset()-2, scanner.getOffset());
				} else if (ch2 == '"' || ch2 == '\\') {
					scanner.delete(scanner.getOffset()-2, scanner.getOffset()-1);
				} else {
					
					// Expect an identifier
					int m_start = scanner.getOffset()-2;
					
					ch = scanner.skipWhite(ch2);
					String key = scanner.readIdentifier(ch);
					
					if (key == null) {
						System.out.println("Failed to read macro name starting with " +	(char)ch);
					}

					SVDBMacroDef sub_m = searchContext(fContext, key);
					List<String> sub_p = null;
					ch = scanner.get_ch();
					
					debug("    ref=\"" + key + "\"");
					
					int m_end = scanner.getOffset();
					
					if (hasParameters(key)) {
						// TODO: Need to expand parameter references in this macro call
						
						debug("    \"" + key + "\" has parameters");
						ch = scanner.skipWhite(ch);
						
						if (ch == '(') {
							sub_p = parse_params(sub_m, scanner);
//							scanner.get_ch();
						}
						m_end = scanner.getOffset();
					} else {
						debug("    \"" + key + "\" doesn't have parameters");
					}
					
					// Now, expand this macro
					if (ch != -1) {
						// Back up if we didn't end by exhausing the buffer. 
						// We don't want to replace the character following the macro
						scanner.unget_ch(ch);
						m_end--;
					} 
					
					debug("    text for expansion ends with " + 
							scanner.getStorage().charAt(m_end-1));
					StringTextScanner scanner_s = new StringTextScanner(
							scanner, m_start, m_end);
					
					if (sub_m != null) {
						expandMacro(scanner_s, sub_m, sub_p);
					} else {
						System.out.println("[ERROR] Macro \"" + key + 
								"\" undefined @ " + fFilename + ":" + fLineno);
						scanner.delete(m_start, m_end-1);
						walkStack();
					}
				}
			}
		}
		
		if (fDebugEn) {
			debug("post=" + scanner.getStorage());
			debug("<-- expandMacroRefs");
		}
	}

	public boolean hasParameters(String key) {
		if (fContext == null) {
			return false;
		}
		
		SVDBMacroDef m = searchContext(fContext, key);
		
		if (m != null) {
			return (m.getParameters().size() != 0);
		} else {
			return false;
		}
	}

	/**
	 * Search the given context for the named macro
	 * 
	 * Strategy is:
	 * - Search the current context for the named macro
	 * - Search the files included in the current context
	 * - Search up the include tree  
	 * @param context
	 * @param key
	 * @return
	 */
	private SVDBMacroDef searchContext(
			SVDBFileTree 	context, 
			String 			key) {
		SVDBMacroDef ret;
		debug_s("--> searchContext(" + context.getFilePath() + ", \"" + key + "\")");
		
		
		if ((ret = fMacroCache.get(key)) == null) {
			if ((ret = searchDown(context, key)) == null) {
				for (SVDBFileTree ib : context.getIncludedByFiles()) {
					ret = searchUp(ib, context, key);
				}
			}
			
			if (ret != null) {
				if (fMacroCache.containsKey(key)) {
					fMacroCache.remove(key);
				}
				fMacroCache.put(key, ret);
			}
		}

		debug_s("<-- searchContext(" + context.getFilePath() + ", \"" + key + "\"");
		return ret;
	}
	
	/**
	 * Search the specified scope and any sub-scopes
	 * 
	 * @param file
	 * @param context
	 * @param key
	 * @return
	 */
	private SVDBMacroDef searchLocal(SVDBFileTree file, SVDBScopeItem context, String key) {
		SVDBMacroDef m = null;
		debug_s("--> searchLocal(" + file.getFilePath() + ", \"" + key + "\"");

		for (SVDBItem it : context.getItems()) {
			debug_s("    it=" + it.getName());
			if (it instanceof SVDBMacroDef && it.getName().equals(key)) {
				m = (SVDBMacroDef)it;
			} else if (it instanceof SVDBScopeItem) {
				m = searchLocal(file, (SVDBScopeItem)it, key);
			}
			
			if (m != null) {
				break;
			}
		}
		
		debug_s("<-- searchLocal(" + file.getFilePath() + ", \"" + key + "\"");
		return m;
	}
	
	private SVDBMacroDef searchDown(SVDBFileTree context, String key) {
		SVDBMacroDef m = null;
		
		debug_s("--> searchDown(" + context.getFilePath() + ", \"" + key + "\")");
		
		if ((m = searchLocal(context, context.getSVDBFile(), key)) == null) {
			for (SVDBFileTree inc : context.getIncludedFiles()) {
				debug_s("    searching included file \"" + inc.getFilePath() + "\"");
				if (inc.getSVDBFile() == null) {
					System.out.println("[TODO] do lookup of inc file \"" + 
							inc.getFilePath() + "\"");
				} else {
					if ((m = searchDown(inc, key)) != null) {
						break;
					}
				}
			}
		}
		
		debug_s("<-- searchDown(" + context.getFilePath() + ", \"" + key + "\")");
		return m;
	}
	
	/**
	 * Search up the file tree. 
	 * 
	 * @param context - The context to search
	 * @param child   - The file that is included by context
	 * @param key     - 
	 * @return
	 */
	private SVDBMacroDef searchUp(
			SVDBFileTree 	context,
			SVDBFileTree	child,
			String 			key) {
		SVDBMacroDef m = null;
		
		debug_s("--> searchUp(" + context.getFilePath() + ", " + key + ")");
		
		if ((m = searchLocal(context, context.getSVDBFile(), key)) == null) {
			for (SVDBFileTree is : context.getIncludedFiles()) {
				
				if (!is.getFilePath().equals(child.getFilePath())) {
					debug_s("    included file: " + is.getFilePath());
				
					if ((m = searchDown(is, key)) == null) {
						for (SVDBFileTree ib : context.getIncludedByFiles()) {
							if ((m = searchUp(ib, context, key)) != null) {
								break;
							}
						}
					}
				}
				
				if (m != null) {
					break;
				}
			}
		}

		debug_s("<-- searchUp(" + context.getFilePath() + ", " + key + ")");
		return m;
	}

	private void walkStack() {
		String key;
		Stack<String> tmp = new Stack<String>();
		tmp.addAll(fExpandStack);
		
		System.out.println("walkStack");
		while (tmp.size() > 0) {
			key = tmp.pop();
			System.out.println("    " + key);
		}
	}
	
	private void debug(String str) {
		if (fDebugEn) {
			System.out.println(str);
		}
	}
	
	private void debug_s(String str) {
		if (fDebugEnS) {
			System.out.println(str);
		}
	}

}

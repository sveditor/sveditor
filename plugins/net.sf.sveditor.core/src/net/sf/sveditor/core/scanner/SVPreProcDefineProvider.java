package net.sf.sveditor.core.scanner;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ISVDBIndex;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMacroDef;

public class SVPreProcDefineProvider implements IDefineProvider {
	private ISVDBIndex					fIndex;
	private SVDBFileTree				fContext;
	
	public SVPreProcDefineProvider() {
	}
	
	public SVPreProcDefineProvider(ISVDBIndex index) {
		fIndex = index;
	}
	
	public void setFileContext(SVDBFileTree context) {
		fContext = context;
	}

	public String getDefineVal(String key, List<String> params) {
		System.out.println("[FIXME] getDefineVal()");
		return "";
	}
	
	public String expandMacro(String str) {
		StringTextScanner scanner = new StringTextScanner(
				new StringBuilder(str));

		debug("--> expandMacro(str): " + str);

		expandMacro(scanner);
		
		debug("<-- expandMacro(str): " + str);
		debug("    Result: " + scanner.getStorage().toString());
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
					"with '`', not " + (char)ch);
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		// Read the macro name
		String key = scanner.readIdentifier(scanner.get_ch());
		
		ch = scanner.skipWhite(scanner.get_ch());
		
		SVDBMacroDef m = searchContext(fContext, key);
		
		if (m == null) {
			System.out.println("[ERROR] macro \"" + key + "\" undefined");
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

			debug("pre-expand: str=" + scanner.getStorage()); 
			expandMacroRefs(new StringTextScanner(scanner, scanner.getOffset()));
			debug("post-expand: str=" + scanner.getStorage()); 
			
			params = parse_params(m, scanner);
			
			scanner_s = new StringTextScanner(scanner, 
					macro_start, scanner.getOffset());
			expandMacro(scanner_s, m, params);
			
			debug("Expansion of " + m.getName() + " is: " +
					scanner.getStorage().toString());
			
			ch = scanner.get_ch();

		} else {
			// Simple -- just replace the text range with the macro text
			StringTextScanner scanner_s = new StringTextScanner(
					scanner, macro_start, scanner.getOffset());
			
			expandMacro(scanner_s, m, null);
			
			debug("Expansion Result: " + scanner_s.getStorage().toString());
			scanner.replace(macro_start, scanner.getOffset(), 
					scanner_s.getStorage().toString());
		}
		
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
		debug("    text=" + scanner.substring(scanner.getOffset(), scanner.getLimit()));
		
		if (expand_params) {
			expand_params = (params.size() == m.getParameters().size());
			if (params.size() != m.getParameters().size()) {
				System.out.println("[ERROR] param count doesn't match: " + 
						params.size() + " vs " + m.getParameters().size());
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
			return;
		}
		
		debug("def=" + m.getDef());
		
		// Replace the text and adjust the limits
		scanner.replace(scanner.getOffset(), scanner.getLimit(), m.getDef());

		// Expand the parameter references within the replacement
		if (expand_params) {
			expandParameterRefs(new StringTextScanner(scanner), 
					m.getParameters(), params);
		}

		// Expand pre-processor references within the replacement
		expandMacroRefs(new StringTextScanner(scanner));
		
		
		debug("    text=" + scanner.getStorage().toString());
		debug("<-- expandMacro(" + m.getName() + ")");
	}
	
	private List<String> parse_params(
			SVDBMacroDef			m,
			StringTextScanner 		scanner) {
		debug("--> parse_params(" + m.getName() + ")");
		debug("    str=" + scanner.getStorage().substring(scanner.getOffset()));
		List<String> params = new ArrayList<String>();
		int ch = scanner.get_ch();
		
		for (int i=0; i<m.getParameters().size(); i++) {
			ch = scanner.skipWhite(ch);
			int p_start = scanner.getOffset()-1;
			
			if (ch == -1) {
				break;
			}
			
			// Skip an argument, including 
			do {
				ch = scanner.get_ch();
				
				if (ch == '(') {
					ch = scanner.skipPastMatch("()");
				}
			} while (ch != -1 && ch != ',' && ch != ')');
			
			int p_end = scanner.getOffset();
			
			String param;
			if (scanner.getStorage().charAt(p_start) == '`') {
				// Need to sub-expand this parameter
				StringTextScanner scanner_s = new StringTextScanner(
						scanner, p_start, p_end-1);
				debug("String passed to expandMacro(1): " + 
						scanner_s.substring(p_start, p_end-1));
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
		
		for (String s : params) {
			debug("Param: \"" + s + "\"");
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

		debug("--> expandParameterRefs");
		debug("pre=" + scanner.getStorage());

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
				// Could skip string...
				scanner.readString(ch);
			}
		}
		
		debug("<-- expandParameterRefs");
		debug("post=" + scanner.getStorage());
	}
	
	private void expandMacroRefs(StringTextScanner scanner) {
		int ch;
		
		debug("--> expandMacroRefs");
		debug("pre=" + scanner.getStorage().substring(scanner.getOffset(), scanner.getLimit()));
		
		while ((ch = scanner.get_ch()) != -1) {
			if (ch == '`') {
				int ch2 = scanner.get_ch();
				
				if (ch2 == '`') {
					// Nothing -- `` is the same as ## in C++ pre-proc
					scanner.delete(scanner.getOffset()-1, scanner.getOffset()+1);
				} else if (ch2 == '"' || ch2 == '\\') {
					System.out.println("[TODO] must delete escaped '" + (char)ch2 + "'");
				} else {
					
					// Expect an identifier
					int m_start = scanner.getOffset()-2;
					
					ch = scanner.skipWhite(ch2);
					String key = scanner.readIdentifier(ch);
					
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
						m_end = scanner.getOffset()+1;
					} else {
						debug("    \"" + key + "\" doesn't have parameters");
					}
					
					// Now, expand this macro
					/*
					debug("first char=" + scanner.getStorage().charAt(m_start));
					debug("    offset=" + scanner.getOffset());
					debug("    char=" + scanner.getStorage().charAt(m_end));
					debug("    send substring: " + scanner.substring(m_start, m_end));
					 */
					
					if (ch != -1) {
						scanner.unget_ch(ch);
					}
					
					StringTextScanner scanner_s = new StringTextScanner(scanner, m_start, m_end-1);
					
					if (sub_m != null) {
						expandMacro(scanner_s, sub_m, sub_p);
					} else {
						System.out.println("[ERROR] Macro \"" + key + "\" undefined");
					}
				}
			}
		}
		
		debug("post=" + scanner.getStorage());
		debug("<-- expandMacroRefs");
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

	private SVDBMacroDef searchContext(
			SVDBFileTree 	context, 
			String 			key) {
		SVDBMacroDef ret = null;
		
		if ((ret = searchLocal(context, key)) != null) {
			return ret;
		}
		
		if ((ret = searchDown(context, key)) != null) {
			return ret;
		}
		
		if ((ret = searchUp(context, key)) != null) {
			return ret;
		}
		

		return ret;
	}
	
	private SVDBMacroDef searchLocal(SVDBFileTree context, String key) {
		SVDBMacroDef m = null;

		for (SVDBItem it : context.getSVDBFile().getItems()) {
			if (it instanceof SVDBMacroDef && it.getName().equals(key)) {
				m = (SVDBMacroDef)it;
				break;
			}
		}
		
		return m;
	}
	
	private SVDBMacroDef searchDown(SVDBFileTree context, String key) {
		SVDBMacroDef m = null;

		for (SVDBFileTree inc : context.getIncludedFiles()) {
			if (inc.getSVDBFile() == null) {
				System.out.println("[TODO] do lookup of inc file \"" + 
						inc.getFilePath().getPath() + "\"");
			} else {
				if ((m = searchLocal(inc, key)) != null) {
					break;
				}
				
				if ((m = searchDown(inc, key)) != null) {
					break;
				}
			}
		}
		
		return m;
	}
	
	private SVDBMacroDef searchUp(SVDBFileTree context, String key) {
		SVDBMacroDef m = null;
		
		for (SVDBFileTree is : context.getIncludedByFiles()) {
			
			if ((m = searchLocal(is, key)) != null) {
				break;
			}

			for (SVDBFileTree inc : is.getIncludedFiles()) {
				if (inc != context) {
					if ((m = searchDown(inc, key)) != null) {
						break;
					}
				}
			}
			
			if (m != null) {
				break;
			}
			
			if ((m = searchUp(is, key)) != null) {
				break;
			}
		}

		return m;
	}


	private SVDBFileTree findFile(String file) {
		return fIndex.findIncludedFile(file);
	}
	
	private void debug(String str) {
//		System.out.println(str);
	}

}

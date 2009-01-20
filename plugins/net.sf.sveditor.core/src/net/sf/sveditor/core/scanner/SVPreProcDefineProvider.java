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
	
	
	public SVPreProcDefineProvider(ISVDBIndex index) {
		fIndex = index;
	}
	
	public void setFileContext(SVDBFileTree context) {
		fContext = context;
	}

	@Override
	public String getDefineVal(String key, List<String> params) {
		if (fContext == null) {
			System.out.println("[ERROR] no context");
			return null;
		}
		
		// Search for the definition up the include tree
		SVDBMacroDef m = searchContext(fContext, key);
		
		if (m != null) {
			// Expand macro
			return expandMacro(m, params);
		} else {
			return null;
		}
	}

	@Override
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
		for (SVDBItem it : context.getSVDBFile().getItems()) {
			if (it instanceof SVDBMacroDef && it.getName().equals(key)) {
				return (SVDBMacroDef)it;
			}
		}
		
		return null;
	}
	
	private SVDBMacroDef searchDown(SVDBFileTree context, String key) {
		for (SVDBFileTree inc : context.getIncludedFiles()) {
			SVDBMacroDef m;
			if (inc.getSVDBFile() == null) {
				System.out.println("[TODO] do lookup of inc file \"" + 
						inc.getFilePath().getPath() + "\"");
			} else {
				if ((m = searchLocal(inc, key)) != null) {
					return m;
				}
				
				if ((m = searchDown(inc, key)) != null) {
					return m;
				}
			}
		}
		
		return null;
	}
	
	private SVDBMacroDef searchUp(SVDBFileTree context, String key) {
		for (SVDBFileTree is : context.getIncludedByFiles()) {
			SVDBMacroDef m;
			
			if ((m = searchLocal(is, key)) != null) {
				return m;
			}
			
			if ((m = searchUp(is, key)) != null) {
				return m;
			}
		}
		
		return null;
	}


	private SVDBFileTree findFile(String file) {
		return fIndex.findIncludedFile(file);
	}

	private String expandMacro(SVDBMacroDef m, List<String> params) {
		System.out.println("--> expandMacro(" + m.getName() + ")");
		StringBuffer sb = new StringBuffer();
		List<String> param_tmp = null;
		StringBuffer tmp_b = null, tmp_b2 = null; 
		
		if (m.getDef() == null) {
			System.out.println("[ERROR] macro definition for key \"" + 
					m.getName() + "\" is null");
			return "";
		}
		
		if (m.getParameters().size() != params.size()) {
			System.out.println("[ERROR] param count doesn't match");
		} else {
			for (int i=0; i<m.getParameters().size(); i++) {
				System.out.println("p=" + m.getParameters().get(i) + 
						" val=" + params.get(i));
			}
		}
		
		System.out.println("def=" + m.getDef());
		
		// Step through the macro
		int idx = 0;
		sb.append(m.getDef());
		while (idx < sb.length()) {
			if (sb.charAt(idx) == '`') {
				int ch2 = -1;
				
				if (idx+1 < sb.length()) {
					idx++;
					ch2 = sb.charAt(idx);
				}
				
				if (ch2 == '`') {
					// Nothing... `` is the same as ## in C++ pre-proc
					sb.delete(idx-1, idx+1);
					idx -= 2;
				} else if (ch2 == '"' || ch2 == '\\') {
					sb.delete(idx-1, idx);
					idx--;
					System.out.println("delete \" or \\: next=" + sb.charAt(idx));
				} else {
					// Expect an identifier

					// recursively expand a macro
					if (tmp_b == null) {
						tmp_b = new StringBuffer();
					}
					if (tmp_b2 == null) {
						tmp_b2 = new StringBuffer();
					}
					tmp_b.setLength(0);
					
					int start = idx;
					// Read in an identifier
					while (idx < sb.length() &&
							Character.isJavaIdentifierPart(sb.charAt(idx))) {
						tmp_b.append(sb.charAt(idx));
						idx++;
					}
					
					String key = tmp_b.toString();
					tmp_b.setLength(0);
					
					if (key.length() == 0) {
						System.out.println("[ERROR] bad pre-processor directive");
					} else {
						if (param_tmp == null) {
							param_tmp = new ArrayList<String>();
						}
						param_tmp.clear();
						
						if (sb.charAt(idx) == '(') {
							idx++; // move past the initial '('
							
							while (idx < sb.length()) {
								int matchLevel = 0;
								
								tmp_b.setLength(0);
								// Inner loop: scan up to ','
								do {
									if (sb.charAt(idx) == '(') {
										matchLevel++;
										tmp_b.append(sb.charAt(idx));
									} else if (sb.charAt(idx) == ')') {
										matchLevel--;
										tmp_b.append(sb.charAt(idx));
									} else if (Character.isJavaIdentifierStart(sb.charAt(idx))) {
										int p_start = tmp_b.length();
										while (idx < sb.length() &&
												Character.isJavaIdentifierPart(sb.charAt(idx))) {
											tmp_b.append(sb.charAt(idx));
											idx++;
										}
										
										String id = tmp_b.substring(p_start);
										int index = m.getParameters().indexOf(id);
										
										if (index != -1 && index < params.size()) {
											String repl = params.get(index);
											tmp_b.replace(p_start, tmp_b.length(), repl);
										}
										idx--;
									} else {
										tmp_b.append(sb.charAt(idx));
									}
									
									idx++;
									
									if (matchLevel == 0 && sb.charAt(idx) == ')') {
										break;
									}
								} while (idx < sb.length());
								
								param_tmp.add(tmp_b.toString());
								
								if (idx < sb.length() && sb.charAt(idx) == ',') {
									idx++;
								}
							}
						}
						String exp = getDefineVal(key, param_tmp);
						
						if (exp != null) {
							System.out.println("Before replace: " + sb.toString());
							sb.replace(start-1, idx, exp);
							System.out.println("After replace: " + sb.toString());
							
							// Go back and rescan the new content for macros
							idx = start;
						} else {
							System.out.println("[WARN] macro \"" + key + "\" undefined");
						}
					}
				}
			} else if (sb.charAt(idx) == '"') {
				do {
					idx++;
				} while (idx < sb.length() &&
						sb.charAt(idx) != '"' && sb.charAt(idx-1) != '\\');
			} else if (Character.isJavaIdentifierStart(sb.charAt(idx))) {
				// Read an identifier
				if (tmp_b == null) {
					tmp_b = new StringBuffer();
				}
				tmp_b.setLength(0);
				
				int start = idx;
				while (idx < sb.length() &&
						Character.isJavaIdentifierPart(sb.charAt(idx))) {
					tmp_b.append((char)sb.charAt(idx));
					idx++;
				}
				
				String key = tmp_b.toString();
				
				// Check whether this identifier matches a macro parameter
				// and, if so, replace the text
				int index = m.getParameters().indexOf(key);
				if (index != -1 && index < params.size()) {
					String repl = params.get(index);
					sb.replace(start, idx, repl);
					
					idx = start + repl.length()-1;
				} else {
					idx--;
				}
			}
			idx++;
		}
		
		System.out.println("<-- expandMacro()");
		return sb.toString();
	}
}

package net.sf.sveditor.core.scanner;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMacroDef;

public class SVPreProcDefineProvider implements IDefineProvider {
	private Map<String, SVDBFileTree>	fFileMap;
	private SVDBFileTree				fContext;
	
	
	public SVPreProcDefineProvider(Map<String, SVDBFileTree> file_map) {
		fFileMap   = file_map;
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
		
		for (SVDBItem it : context.getSVDBFile().getItems()) {
			if (it instanceof SVDBMacroDef && it.getName().equals(key)) {
				return (SVDBMacroDef)it;
			} else if (it instanceof SVDBInclude) {
				// Search the include scope
				SVDBFileTree ctxt = findFile(it.getName());
				
				if (ctxt != null) {
					
				}
				// Search the including scope (and any parents)
			}
		}
		
		for (SVDBFileTree is : context.getIncludedByFiles()) {
			SVDBMacroDef m;
			
			if ((m = searchContext(is, key)) != null) {
				return m;
			}
		}

		return null;
	}


	private SVDBFileTree findFile(String file) {
		Iterator<String> it = fFileMap.keySet().iterator();
		
		while (it.hasNext()) {
			String key = it.next();
			
			if (key.endsWith(file)) {
				return fFileMap.get(key);
			}
		}
		
		return null;
	}

	private String expandMacro(SVDBMacroDef m, List<String> params) {
		StringBuffer sb = new StringBuffer();
		List<String> param_tmp = null;
		StringBuffer tmp_b = null; 
		String md = m.getDef(); 
		
		// Step through the macro
		int idx = 0;
		while (idx < md.length()) {
			if (md.charAt(idx) == '`') {
				int ch2 = (idx+1 < md.length())?md.charAt(++idx):-1;
				
				if (ch2 == '`') {
					// Nothing... `` is the same as ## in C++ pre-proc
				} else if (ch2 == '"') {
					sb.append('"');
				} else if (ch2 == '\\') {
					sb.append('\\');
				} else {
					// Expect an identifier
					
					if (ch2 != -1) {
						idx--;
					}
					
					// recursively expand a macro
					if (tmp_b == null) {
						tmp_b = new StringBuffer();
					}
					tmp_b.setLength(0);
					
					// Read in an identifier
					while (idx < md.length() &&
							Character.isJavaIdentifierPart(md.charAt(idx))) {
						tmp_b.append(md.charAt(idx++));
					}
					
					String key = tmp_b.toString();
					tmp_b.setLength(0);
					
					if (sb.length() == 0) {
						System.out.println("[ERROR] bad pre-processor directive");
					} else {
						if (param_tmp == null) {
							param_tmp = new ArrayList<String>();
						}
						param_tmp.clear();
						
						if (md.charAt(idx) == '(') {
							idx++; // move past the initial '('
							
							while (idx < md.length()) {
								int matchLevel = 0;
								
								// Inner loop: scan up to ','
								do {
									if (md.charAt(idx) == '(') {
										matchLevel++;
									} else if (md.charAt(idx) == ')') {
										matchLevel--;
									}
									tmp_b.append(md.charAt(idx));
									
									idx++;
									
									if (matchLevel == 0 && md.charAt(idx) == ')') {
										break;
									}
								} while (idx < md.length());
								
								param_tmp.add(tmp_b.toString());
								
								if (idx < md.length() && md.charAt(idx) == ',') {
									idx++;
								}
							}
						}
						String exp = getDefineVal(key, param_tmp);
						
						if (exp != null) {
							sb.append(exp);
						} else {
							System.out.println("[WARN] macro \"" + key + "\" undefined");
						}
					}
				}
			} else {
				sb.append(md.charAt(idx));
			}
		}
		
		return sb.toString();
	}
}

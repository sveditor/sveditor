package net.sf.sveditor.core.argfile.parser;


public class SVArgFileUtils {
	
	public static String expandVars(String path, ISVArgFileVariableProvider var_provider) {
		boolean workspace_prefix = path.startsWith("${workspace_loc}");
		String exp_path = path;
		
		if (workspace_prefix) {
			exp_path = exp_path.substring("${workspace_loc}".length());
		}
		
		StringBuilder sb = new StringBuilder(exp_path);
		StringBuilder tmp = new StringBuilder();

		int found_var = 1;
		
		while (found_var == 1)  {
			int idx = 0;
			found_var = 0;
	
			while (idx < sb.length()) {
				if (sb.charAt(idx) == '$') {
					tmp.setLength(0);
	
					int start = idx, end;
					String key, val=null;
					idx++;
					if (sb.charAt(idx) == '{') {
						idx++;
	
						while (idx < sb.length() && sb.charAt(idx) != '}') {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						if (idx < sb.length()) {
							end = ++idx;
						} else {
							end = idx;
						}
					} else {
						while (idx < sb.length() && 
								sb.charAt(idx) != '/' && !Character.isWhitespace(sb.charAt(idx))) {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						end = idx;
					}
	
					key = tmp.toString();
					val = var_provider.expandVar(key);
					
					if (val != null) {
						found_var = 1;
					
						// Try to replace /[a-zA-Z]: with [a-zA-Z]:
						System.out.println("val=" + val);
						if (val.length() >= 3 && 
								val.charAt(0) == '/' &&
								val.charAt(2) == ':' &&
								((val.charAt(1) >= 'a' && val.charAt(1) <= 'z') ||
								 (val.charAt(1) >= 'A' && val.charAt(1) <= 'Z'))) {
							val = val.substring(1);
							System.out.println("new val=" + val);
						}
						sb.replace(start, end, val);
						break;	// need to break because our string has been changed, start again
					}
				} else {
					idx++;
				}
			}
		}
			
		exp_path = sb.toString();
			
		if (workspace_prefix) {
			exp_path = "${workspace_loc}" + exp_path;
		}
		
		return exp_path;
	}

}

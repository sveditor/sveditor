package net.sf.sveditor.core.db.search;

import java.util.regex.Pattern;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBContentAssistIncludeNameMatcher extends SVDBFindContentAssistNameMatcher {
	private static Pattern					fWinPathPattern;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}

	@Override
	public boolean match(SVDBItem it, String name) {
		if (it.getType() == SVDBItemType.File) {
			String norm_path = fWinPathPattern.matcher(it.getName()).replaceAll("/");
			String last_elem = norm_path;
			if (norm_path.indexOf('/') != -1) {
				last_elem = norm_path.substring(norm_path.lastIndexOf('/')+1);
			}
			
			last_elem = last_elem.toLowerCase();
			name = name.toLowerCase();
			
			return last_elem.startsWith(name);
		} else {
			return super.match(it, name);
		}
	}

}

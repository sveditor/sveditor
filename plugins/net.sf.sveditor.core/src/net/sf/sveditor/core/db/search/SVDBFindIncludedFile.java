package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class SVDBFindIncludedFile {
	
	private ISVDBIndexIterator				fIndexIterator;
	private static Pattern					fWinPathPattern;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	public SVDBFindIncludedFile(ISVDBIndexIterator index_it) {
		fIndexIterator = index_it;
	}
	
	public List<SVDBFile> find(String name, boolean match_prefix) {
		ISVDBItemIterator<SVDBItem> item_it = fIndexIterator.getItemIterator();
		List<SVDBFile> ret = new ArrayList<SVDBFile>();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			if (it.getType() == SVDBItemType.File) {
				String f = it.getName();
				String norm_path = fWinPathPattern.matcher(f).replaceAll("/");
				
				if (match_prefix) {
					String last_elem;
					if (norm_path.indexOf('/') != -1) {
						last_elem = norm_path.substring(norm_path.lastIndexOf('/')+1);
					} else {
						last_elem = norm_path;
					}
					if (last_elem.startsWith(name)) {
						ret.add((SVDBFile)it);
					}
				} else {
					if (norm_path.endsWith(name)) {
						ret.add((SVDBFile)it);
					}
				}
			}
		}
		
		return ret;
	}

}

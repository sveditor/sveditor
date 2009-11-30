package net.sf.sveditor.core.db.search;

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
	
	public SVDBFile find(String name) {
		ISVDBItemIterator<SVDBItem> item_it = fIndexIterator.getItemIterator();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			System.out.println("IncludeFinder: " + it.getType() + " " + it.getName());
			
			if (it.getType() == SVDBItemType.File) {
				String f = it.getName();
				String norm_path = fWinPathPattern.matcher(f).replaceAll("/");
				
				if (norm_path.endsWith(name)) {
					return (SVDBFile)it;
				}
			}
		}
		
		return null;
	}

}

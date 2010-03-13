package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBPackageItemFinder {
	private ISVDBIndexIterator			fIndexIt;
	private ISVDBFindNameMatcher		fMatcher;
	
	public SVDBPackageItemFinder(
			ISVDBIndexIterator		index_it,
			ISVDBFindNameMatcher 	matcher) {
		fIndexIt = index_it;
		fMatcher = matcher;
	}
	
	public List<SVDBItem> find(
			SVDBPackageDecl 	pkg, 
			String 				name) {
		SVDBFindIncludedFile inc_finder = new SVDBFindIncludedFile(fIndexIt);
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (SVDBItem it : pkg.getItems()) {
			if (it.getType() == SVDBItemType.Include) {
				List<SVDBFile> file = inc_finder.find(it.getName());
				
				if (file.size() > 0) {
					find(file.get(0), ret, name);
				}
			} else if (it.getType() == SVDBItemType.Class) {
				if (fMatcher.match(it, name)) {
					ret.add(it);
				}
			}
		}
		
		
		return ret;
	}
	
	private void find(SVDBFile file, List<SVDBItem> items, String name) {
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Class) {
				if (fMatcher.match(it, name)) {
					items.add(it);
				}
			}
		}
	}

}

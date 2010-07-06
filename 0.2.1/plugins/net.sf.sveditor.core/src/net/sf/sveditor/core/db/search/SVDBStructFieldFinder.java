package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;

public class SVDBStructFieldFinder {
	private ISVDBFindNameMatcher				fMatcher;
	
	public SVDBStructFieldFinder(ISVDBFindNameMatcher matcher) {
		fMatcher = matcher;
	}
	
	public List<SVDBItem> find(SVDBTypeInfoStruct struct, String name) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (SVDBItem it : struct.getFields()) {
			if (fMatcher.match(it, name)) {
				ret.add(it);
			}
		}
		
		return ret;
	}

}

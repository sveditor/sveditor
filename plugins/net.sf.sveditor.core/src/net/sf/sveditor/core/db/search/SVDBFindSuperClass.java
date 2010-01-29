package net.sf.sveditor.core.db.search;

import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBFindSuperClass {
	
	ISVDBIndexIterator				fIndexIterator;
	private ISVDBFindNameMatcher	fMatcher;
	
	public SVDBFindSuperClass(
			ISVDBIndexIterator 		index_it, 
			ISVDBFindNameMatcher	matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
	}
	
	public SVDBModIfcClassDecl find(SVDBModIfcClassDecl cls) {
		if (cls.getSuperClass() != null) {
			SVDBFindNamedModIfcClassIfc finder = 
				new SVDBFindNamedModIfcClassIfc(fIndexIterator, fMatcher);
			
			List<SVDBModIfcClassDecl> ret = finder.find(cls.getSuperClass());
			
			return (ret.size() > 0)?ret.get(0):null;
		} else {
			return null;
		}
	}

}

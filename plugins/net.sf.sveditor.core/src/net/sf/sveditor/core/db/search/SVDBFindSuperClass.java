package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBFindSuperClass {
	
	ISVDBIndexIterator				fIndexIterator;
	
	public SVDBFindSuperClass(ISVDBIndexIterator index_it) {
		fIndexIterator = index_it;
	}
	
	public SVDBModIfcClassDecl find(SVDBModIfcClassDecl cls) {
		if (cls.getSuperClass() != null) {
			SVDBFindNamedModIfcClassIfc finder = 
				new SVDBFindNamedModIfcClassIfc(fIndexIterator);
			
			return finder.find(cls.getSuperClass());
		} else {
			return null;
		}
	}

}

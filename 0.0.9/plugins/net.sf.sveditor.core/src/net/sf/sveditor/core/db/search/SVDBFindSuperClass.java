package net.sf.sveditor.core.db.search;

import java.util.List;

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
			
			List<SVDBModIfcClassDecl> ret = finder.find(cls.getSuperClass(), false);
			
			return (ret.size() > 0)?ret.get(0):null;
		} else {
			return null;
		}
	}

}

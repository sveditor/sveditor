package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBFindByNameInClassHierarchy {
	private ISVDBIndexIterator		fIndexIterator;
	private LogHandle				fLog;
	
	
	public SVDBFindByNameInClassHierarchy(ISVDBIndexIterator index_it) {
		fIndexIterator = index_it;
		fLog = LogFactory.getDefault().getLogHandle("FindByNameInClassHierarchy");
	}
	
	public List<SVDBItem> find(
			SVDBScopeItem 		scope, 
			String 				id,
			boolean				match_prefix,
			SVDBItemType	...	types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		fLog.debug("--> find(" + ((scope != null)?scope.getName():null) + " \"" + id + "\")");
		for (SVDBItemType t : types) {
			fLog.debug("    TYPE " + t);
		}
		
		while (scope != null && scope.getType() != SVDBItemType.Class &&
				scope.getType() != SVDBItemType.Struct) {
			fLog.debug("Searching up-scope (current is " + scope.getType() + 
					" " + scope.getName() + ")");
			scope = scope.getParent();
		}
		
		if (scope == null) {
			fLog.debug("Failed to find Class/Struct scope");
			fLog.debug("<-- find(\"" + id + "\") returns " + ret.size() + " results");
			return ret;
		}
		
		// Now, search through the scope and the class hierarchy
		while (scope != null) {
			fLog.debug("Searching scope \"" + scope.getName() + "\"");
			for (SVDBItem it : scope.getItems()) {
				boolean matches = (types.length == 0);
				
				for (SVDBItemType type : types) {
					if (it.getType() == type) {
						matches = true;
						break;
					}
				}

				if (matches) {
					if (match_prefix) {
						if (id.equals("") || it.getName().startsWith(id)) {
							ret.add(it);
						}
					} else {
						if (it.getName().equals(id)) {
							ret.add(it);
						}
					}
				}
			}

			SVDBFindSuperClass finder = new SVDBFindSuperClass(fIndexIterator);
			scope = finder.find((SVDBModIfcClassDecl)scope);
		}
		
		fLog.debug("<-- find(\"" + id + "\") returns " + ret.size() + " results");
		return ret;
	}
}

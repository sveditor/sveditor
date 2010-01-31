package net.sf.sveditor.core.db.search;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;

public interface ISVDBIndexSearcher {
	
	SVDBModIfcClassDecl findNamedModClassIfc(String name);
	
	
	/** 
	 * Visits items of a particular type
	 * 
	 * @param visitor
	 * @param types
	 */
	void visitItems(
			ISVDBItemVisitor		visitor,
			SVDBItemType  			type);

	void visitItemsInTypeHierarchy(
			SVDBScopeItem			scope,
			ISVDBItemVisitor		visitor);

	List<SVDBItem> findByNameInScopes(
			String					name,
			SVDBScopeItem			scope,
			boolean					stop_on_first_match,
			SVDBItemType	...		type_filter);

	List<SVDBItem> findVarsByNameInScopes(
			String					name,
			SVDBScopeItem			scope,
			boolean					stop_on_first_match);

	List<SVDBItem> findByName(
			String					name,
			SVDBItemType	...		type_filter);
	
	List<SVDBItem> findByNameInClassHierarchy(
			String					name,
			SVDBScopeItem			scope,
			SVDBItemType	...		type_filter);
	
	SVDBModIfcClassDecl findSuperClass(SVDBModIfcClassDecl cls);
	
	SVDBFile findIncludedFile(String path);
		
}

package net.sf.sveditor.core.db.index.sv;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.AbstractDeclCacheBuilder;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.cache.ISVDBDeclCacheInt;

public class SVDeclCacheBuilder extends AbstractDeclCacheBuilder {
	private static final Set<SVDBItemType>		fGlobalScopeItems;

	static {
		fGlobalScopeItems = new HashSet<SVDBItemType>();
		fGlobalScopeItems.add(SVDBItemType.Function);
		fGlobalScopeItems.add(SVDBItemType.Task);
		fGlobalScopeItems.add(SVDBItemType.VarDeclItem);
		fGlobalScopeItems.add(SVDBItemType.TypedefStmt);
		fGlobalScopeItems.add(SVDBItemType.ClassDecl);
		fGlobalScopeItems.add(SVDBItemType.PackageDecl);
		fGlobalScopeItems.add(SVDBItemType.Covergroup);
		fGlobalScopeItems.add(SVDBItemType.InterfaceDecl);
		fGlobalScopeItems.add(SVDBItemType.ModuleDecl);
		fGlobalScopeItems.add(SVDBItemType.ProgramDecl);
	}
	
	public SVDeclCacheBuilder() {
		super("SVDeclCacheBuilder", null, null, null, null, -1);
		System.out.println("TODO: SVDeclCacheBuilder()");
	}

	public SVDeclCacheBuilder(
			List<SVDBDeclCacheItem> decl_list,
			ISVDBDeclCacheInt		decl_cache,
			Set<Integer>			included_files,
			Set<String>				missing_includes,
			int						rootfile_id) {
		super("SVDeclCacheBuilder", decl_list, decl_cache,
				included_files, missing_includes,
				rootfile_id);
	}
	
	@Override
	protected boolean should_add(ISVDBItemBase item) {
		if (fDisabledDepth > 0) {
			return false;
		} else if (fScopeStack.size() == 0) {
			// Global scope
			return item.getType().isElemOf(fGlobalScopeItems);
		} else {
			return true;
		}
	}
}

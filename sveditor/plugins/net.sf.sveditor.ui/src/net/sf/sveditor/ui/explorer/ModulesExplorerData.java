package net.sf.sveditor.ui.explorer;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;

public class ModulesExplorerData extends DeferredProjectDataProvider {
	
	public ModulesExplorerData(IProjectPathsData p) {
		super(p, "Modules");
	}

	public Object[] getChildrenDeferred(Object parent) {
		IProjectPathsData p = (IProjectPathsData)parent;
		while (p.getParent(p) != null) {
			p = (IProjectPathsData)p.getParent(p);
		}
		ISVDBIndexIterator index_it = ((ProjectPathsData)p).getIndexIt();

		List<SVDBDeclCacheItem> modules = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), "",
				new SVDBFindByTypeMatcher(SVDBItemType.ModuleDecl));		

		DeclCacheItem children[] = new DeclCacheItem[modules.size()];
		for (int i=0; i<modules.size(); i++) {
			children[i] = new DeclCacheItem(this, modules.get(i));
		}
		
		return children;
	}
	
}

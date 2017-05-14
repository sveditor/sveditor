package net.sf.sveditor.ui.explorer;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;

public class ClassesExplorerData extends DeferredProjectDataProvider {
	
	public ClassesExplorerData(IProjectPathsData p) {
		super(p, "Classes");
	}

	@Override
	public Object[] getChildrenDeferred(Object parent) {
		IProjectPathsData p = (IProjectPathsData)parent;
		while (p.getParent(p) != null) {
			p = (IProjectPathsData)p.getParent(p);
		}
		ISVDBIndexIterator index_it = ((ProjectPathsData)p).getIndexIt();

		List<SVDBDeclCacheItem> classes = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), "",
				new SVDBFindByTypeMatcher(SVDBItemType.ClassDecl));		

		DeclCacheItem children[] = new DeclCacheItem[classes.size()];
		for (int i=0; i<classes.size(); i++) {
			children[i] = new DeclCacheItem(this, classes.get(i));
		}
		
		return children;		
	}

}

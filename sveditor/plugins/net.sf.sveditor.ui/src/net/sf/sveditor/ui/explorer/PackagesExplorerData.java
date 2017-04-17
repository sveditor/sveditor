package net.sf.sveditor.ui.explorer;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;

public class PackagesExplorerData implements IProjectPathsData {
	private IProjectPathsData		fParent;
	
	public PackagesExplorerData(IProjectPathsData p) {
		fParent = p;
	}

	@Override
	public String getName() {
		return "Packages";
	}

	@Override
	public Object getParent(Object element) {
		return fParent;
	}
	
	@Override
	public boolean hasChildren() {
		// Provisional
		return true;
	}

	@Override
	public Object[] getChildren(Object parent) {
		System.out.println("Packages.getChildren");
		// Get the root
		IProjectPathsData p = fParent;
		while (p.getParent(p) != null) {
			p = (IProjectPathsData)p.getParent(p);
		}
		ISVDBIndexIterator index_it = ((ProjectPathsData)p).getIndexIt();
		
		List<SVDBDeclCacheItem> packages = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"", new SVDBFindByTypeMatcher(SVDBItemType.PackageDecl));
		
		DeclCacheItem ret[] = new DeclCacheItem[packages.size()];
		
		for (int i=0; i<packages.size(); i++) {
			ret[i] = new DeclCacheItem(this, packages.get(i));
		}
		
		return ret;
	}

}

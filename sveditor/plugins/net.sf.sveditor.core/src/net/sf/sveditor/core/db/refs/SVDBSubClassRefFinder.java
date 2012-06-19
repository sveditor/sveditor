package net.sf.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBSubClassRefFinder {
	
	public static List<SVDBClassDecl> find(
			ISVDBDeclCache 	decl_cache,
			String			clsname) {
		List<SVDBClassDecl> ret = new ArrayList<SVDBClassDecl>();
		List<SVDBRefCacheItem> cache_items = decl_cache.findReferences(
				new NullProgressMonitor(), clsname, new SVDBTypeRefMatcher());
		
		for (SVDBRefCacheItem item : cache_items) {
			List<SVDBRefItem> ref_items = item.findReferences(new NullProgressMonitor());
			// Matching items will be a class with a super-class of <clsname>
			for (SVDBRefItem ref_item : ref_items) {
				if (ref_item.getLeaf().getType() == SVDBItemType.ClassDecl) {
					SVDBClassDecl cls = (SVDBClassDecl)ref_item.getLeaf();
					if (cls.getSuperClass().getName().equals(clsname)) {
						ret.add(cls);
					}
				}
			}
		}
		return ret;
	}

}

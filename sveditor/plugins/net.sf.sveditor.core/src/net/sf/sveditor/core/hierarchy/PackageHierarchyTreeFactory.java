package net.sf.sveditor.core.hierarchy;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class PackageHierarchyTreeFactory {
	private ISVDBIndexIterator			fIndexIt;
	
	public PackageHierarchyTreeFactory(ISVDBIndexIterator it) {
		fIndexIt = it;
	}
	
	private static final Set<SVDBItemType>		fIncludedRootTypes;
	
	static {
		fIncludedRootTypes = new HashSet<SVDBItemType>();
		fIncludedRootTypes.add(SVDBItemType.TypeInfoEnum);
		fIncludedRootTypes.add(SVDBItemType.TypedefStmt);
		fIncludedRootTypes.add(SVDBItemType.ClassDecl);
		fIncludedRootTypes.add(SVDBItemType.VarDeclStmt);
	}

	public HierarchyTreeNode build(SVDBDeclCacheItem pkg) {
		HierarchyTreeNode root = new HierarchyTreeNode(
				null, pkg.getName(), pkg.getSVDBItem());
	
		List<SVDBDeclCacheItem> contents = fIndexIt.findPackageDecl(
				new NullProgressMonitor(), pkg);
		
		for (SVDBDeclCacheItem c : contents) {
			if (c.getType() == SVDBItemType.ImportStmt) {
				System.out.println("import stmt");
			} else if (c.getType().isElemOf(fIncludedRootTypes)) {
				HierarchyTreeNode child = new HierarchyTreeNode(root,
						c.getName(), c.getSVDBItem());
				root.addChild(child);
			} else if (c.getType().isElemOf(SVDBItemType.Task, SVDBItemType.Function)) {
				// Only add tasks and functions if they're global (ie don't have '::' in the name
				if (!c.getName().contains("::")) {
					HierarchyTreeNode child = new HierarchyTreeNode(root,
							c.getName(), c.getSVDBItem());
					root.addChild(child);
				}
			}
		}
	
		return root;
	}
	
}

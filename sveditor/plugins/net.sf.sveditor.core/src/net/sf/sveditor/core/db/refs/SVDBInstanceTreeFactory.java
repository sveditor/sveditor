package net.sf.sveditor.core.db.refs;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBInstanceTreeFactory {
	private ISVDBIndexIterator			fIndexIt;
	
	public SVDBInstanceTreeFactory(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
	}

	public SVDBInstanceTreeNode build(IProgressMonitor monitor, SVDBModIfcDecl root) {
		String typename = root.getName();
		SVDBInstanceTreeNode ret = new SVDBInstanceTreeNode(root);

		build(ret, typename);
	
		return ret;
	}
	
	private void build(SVDBInstanceTreeNode parent, String typename) {
		SVDBRefCollectorVisitor visitor = new SVDBRefCollectorVisitor();
		SVDBRefSearchSpecModIfcRefsByName ref_spec = new SVDBRefSearchSpecModIfcRefsByName(typename);
		
		fIndexIt.execOp(new NullProgressMonitor(), 
				new SVDBFindReferencesOp(ref_spec, visitor), false);
		
		// Now, build out the next level of references
		for (SVDBRefItem ref_it : visitor.getItemList()) {
			ISVDBItemBase it = ref_it.getLeaf();
			
			if (it.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInst inst = (SVDBModIfcInst)it;
				ISVDBChildItem inst_parent = inst;

				while (inst_parent != null && !inst_parent.getType().isElemOf(
						SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl)) {
					inst_parent = inst_parent.getParent();
				}

				if (inst_parent != null) {
					for (ISVDBItemBase it_i : inst.getChildren()) {
						SVDBInstanceTreeNode n = new SVDBInstanceTreeNode(it_i);
						parent.addInstantiation(n);
						build(n, ((SVDBModIfcDecl)inst_parent).getName());
					}
				}
			} else {
				// Not sure what to do. Not expected
			}
		}		
	}
}

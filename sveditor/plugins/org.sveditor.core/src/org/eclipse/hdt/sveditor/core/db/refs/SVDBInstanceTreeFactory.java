/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.refs;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInst;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInstItem;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;

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

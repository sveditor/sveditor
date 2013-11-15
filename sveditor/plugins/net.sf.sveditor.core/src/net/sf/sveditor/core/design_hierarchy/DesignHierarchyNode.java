package net.sf.sveditor.core.design_hierarchy;

import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class DesignHierarchyNode {
	private ISVDBIndexIterator		fIndexIt;
	private Object					fTarget;
	private Object					fParent;
	
	public DesignHierarchyNode(
			ISVDBIndexIterator 	index_it, 
			Object 				target,
			Object				parent) {
		fIndexIt = index_it;
		fTarget = target;
		fParent = parent;
	}
	
	public ISVDBIndexIterator getIndexIt() {
		return fIndexIt;
	}
	
	public Object getTarget() {
		return fTarget;
	}
	
	public Object getParent() {
		return fParent;
	}

}

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
package org.sveditor.core.design_hierarchy;

import org.sveditor.core.db.index.ISVDBIndexIterator;

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

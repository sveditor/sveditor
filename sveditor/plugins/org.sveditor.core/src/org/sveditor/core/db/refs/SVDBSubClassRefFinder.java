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
package org.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.index.ISVDBDeclCache;

public class SVDBSubClassRefFinder {
	
	public static List<SVDBClassDecl> find(
			ISVDBDeclCache 	decl_cache,
			String			clsname) {
		List<SVDBClassDecl> ret = new ArrayList<SVDBClassDecl>();
		/** MSB:
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
		 */
		return ret;
	}

}

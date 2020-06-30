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


public class SVDBTypeRefMatcher implements ISVDBRefVisitor {
	
	

	@Override
	public void visitRef(ISVDBRefSearchSpec ref_spec, SVDBRefItem item) {
		// TODO Auto-generated method stub
	}

	/** MSB:
	public void find_matches(
			List<SVDBRefCacheItem>	matches,
			SVDBRefCacheEntry 		item, 
			String 					name) {
		if (item.getRefSet(SVDBRefType.TypeReference).contains(name)) {
			matches.add(new SVDBRefCacheItem(item, null, SVDBRefType.TypeReference, name));
		}
	}
	 */

}

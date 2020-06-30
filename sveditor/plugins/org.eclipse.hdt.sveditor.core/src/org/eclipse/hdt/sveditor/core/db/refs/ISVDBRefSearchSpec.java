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

import java.util.Stack;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;


public interface ISVDBRefSearchSpec {
	
	enum NameMatchType {
		Any,			// Ignore name
		Equals,
		MayContain		// Perform a quick search to see if there may be references
	}
	
	NameMatchType getNameMatchType();
	
	String getName();

	/**
	 * Check whether a given reference matches the spec
	 * 
	 * @param loc
	 * @param type
	 * @param scope
	 * @param name
	 * @return
	 */
	boolean matches(
			long 					loc, 
			SVDBRefType 			type, 
			Stack<ISVDBItemBase> 	scope, 
			String 					name);
	
}

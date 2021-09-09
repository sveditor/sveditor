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

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBRefFinder {

	/**
	 * Locate the matches referred to by 'item'
	 * 
	 * @param item
	 * @return
	 */
	void findReferences(
			IProgressMonitor 		monitor, 
			ISVDBRefSearchSpec		ref_spec,
			ISVDBRefVisitor			ref_matcher);
	
}

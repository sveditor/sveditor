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
package org.eclipse.hdt.sveditor.core.db.index;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexOperation {
	
//	void pre_operation(ISVDBIndex index);

	/**
	 * Execute the operation
	 * 
	 * @param index
	 */
	void index_operation(IProgressMonitor monitor, ISVDBIndex index);

//	int operation_depth();
	
//	void post_operation(ISVDBIndex index);
	

}

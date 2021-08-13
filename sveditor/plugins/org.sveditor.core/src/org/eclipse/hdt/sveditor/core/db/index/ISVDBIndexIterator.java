/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.db.index;

import org.sveditor.core.db.refs.ISVDBRefFinder;


public interface ISVDBIndexIterator extends 
	ISVDBDeclCache,
	ISVDBMarkerFinder,
	ISVDBIncludeFilesFinder,
	ISVDBIndexOperationRunner,
	ISVDBIndexFileStructProvider,
	ISVDBRefFinder {

	/**
	 * This method is deprecated. The 'findGlobal' methods should be
	 * used instead
	 * 
	 * @param monitor
	 * @return
	@Deprecated
	ISVDBItemIterator 		getItemIterator(IProgressMonitor monitor);
	 */

}

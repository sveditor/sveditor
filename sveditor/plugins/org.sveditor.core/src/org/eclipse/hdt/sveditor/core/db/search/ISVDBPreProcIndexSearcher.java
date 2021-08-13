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


package org.eclipse.hdt.sveditor.core.db.search;

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBFile;

public interface ISVDBPreProcIndexSearcher {
	
	/**
	 * Search the pre-processor view of files looking for the file 
	 * with the specified path
	 * 
	 * @param path
	 * @return
	 */
	List<SVDBSearchResult<SVDBFile>> findPreProcFile(String path, boolean search_shadow);
	
	List<SVDBSearchResult<SVDBFile>> findIncParent(SVDBFile file);

}

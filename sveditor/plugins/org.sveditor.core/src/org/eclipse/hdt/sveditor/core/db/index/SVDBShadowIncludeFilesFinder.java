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
package org.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

/**
 * Implements an include files finder for a specific directory
 * 
 * @author ballance
 *
 */
public class SVDBShadowIncludeFilesFinder implements ISVDBIncludeFilesFinder {
	private List<String>					fDirList;
	
	public SVDBShadowIncludeFilesFinder(String dir) {
		fDirList = new ArrayList<String>();
		fDirList.add(dir);
	}

	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		return SVDBFindIncFileUtils.findIncludeFiles(
				null,
				new SVDBWSFileSystemProvider(),
				fDirList,
				root, flags);		
	}

}

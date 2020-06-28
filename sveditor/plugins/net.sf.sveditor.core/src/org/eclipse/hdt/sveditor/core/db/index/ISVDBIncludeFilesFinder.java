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

import java.util.List;

public interface ISVDBIncludeFilesFinder {

	int FIND_INC_SV_FILES      = 0x01;
	int FIND_INC_ARG_FILES     = 0x02;
	int FIND_INC_ALL_FILES     = 0x04;

	/**
	 * findIncludeFiles()
	 * 
	 * Locates include paths 
	 */
	List<SVDBIncFileInfo> findIncludeFiles(String root, int flags);
}

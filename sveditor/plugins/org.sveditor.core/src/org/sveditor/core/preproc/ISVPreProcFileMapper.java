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
package org.sveditor.core.preproc;

/**
 * SVEditor applies a File ID to each item within an index.
 * Implementations of the ISVPreProcFileMapper convert
 * a file path to a unique (on an index basis) id.
 * 
 * @author ballance
 *
 */
public interface ISVPreProcFileMapper {
	
	int mapFilePathToId(String path, boolean add);
	
	String mapFileIdToPath(int id);

}

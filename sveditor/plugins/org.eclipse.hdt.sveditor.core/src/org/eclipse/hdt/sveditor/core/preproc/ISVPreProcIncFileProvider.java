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
package org.eclipse.hdt.sveditor.core.preproc;

import java.io.InputStream;
import java.util.List;

import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTreeMacroList;

public interface ISVPreProcIncFileProvider {

	/**
	 * 
	 * @param incfile
	 * @return
	 */
	Tuple<String, List<SVDBFileTreeMacroList>> findCachedIncFile(String incfile);

	public void addCachedIncFile(String incfile, String rootfile);
	
	/**
	 * 
	 * @param incfile
	 * @return Tuple of <FullPath, Data> or NULL if the file
	 *  cannot be located
	 */
	Tuple<String, InputStream> findIncFile(String incfile);

}

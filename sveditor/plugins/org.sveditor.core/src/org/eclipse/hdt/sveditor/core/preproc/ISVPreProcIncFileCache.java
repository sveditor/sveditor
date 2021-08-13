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

import java.util.Map;

import org.sveditor.core.Tuple;

public interface ISVPreProcIncFileCache {
	
	Tuple<String, Map<String, String>> findIncCache(
			String 					incfile, 
			Map<String, String> 	references);

	void setIncCache(
			String					incpath,
			String					fullpath,
			Map<String, String>		references);
}

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


package org.eclipse.hdt.sveditor.core.db;

import java.io.InputStream;
import java.util.List;

import org.eclipse.hdt.sveditor.core.parser.SVLanguageLevel;

public interface ISVDBFileFactory {
	
	void init(InputStream in, String filename);

	@Deprecated
	SVDBFile parse(
			InputStream 		in, 
			String 				filename, 
			List<SVDBMarker> 	markers);
	
	SVDBFile parse(
			SVLanguageLevel		language_level,
			InputStream 		in, 
			String 				filename, 
			List<SVDBMarker> 	markers);

}

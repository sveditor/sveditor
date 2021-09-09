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


package org.sveditor.core.db.search;

import java.io.File;

import org.sveditor.core.SVFileUtils;
import org.sveditor.core.db.ISVDBNamedItem;
import org.sveditor.core.db.SVDBItemType;

public class SVDBOpenDeclarationIncludeNameMatcher extends
		SVDBFindDefaultNameMatcher {

	@Override
	public boolean match(ISVDBNamedItem it, String name) {
		if (it.getType() == SVDBItemType.File) {
			String norm_path = SVFileUtils.normalize(it.getName());
			String basename = new File(name).getName();
			
			return (norm_path.endsWith(name) || norm_path.endsWith(basename)); 
		} else {
			return super.match(it, name);
		}
	}
}

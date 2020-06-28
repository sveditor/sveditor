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

import java.util.regex.Pattern;

import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBContentAssistIncludeNameMatcher extends SVDBFindContentAssistNameMatcher {
	private static Pattern					fWinPathPattern;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}

	@Override
	public boolean match(ISVDBNamedItem it, String name) {
		if (it.getType() == SVDBItemType.File) {
			String norm_path = fWinPathPattern.matcher(it.getName()).replaceAll("/");
			String last_elem = norm_path;
			if (norm_path.indexOf('/') != -1) {
				last_elem = norm_path.substring(norm_path.lastIndexOf('/')+1);
			}
			
			last_elem = last_elem.toLowerCase();
			name = name.toLowerCase();
			
			return last_elem.startsWith(name);
		} else {
			return super.match(it, name);
		}
	}
}

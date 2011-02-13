/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.search;

import java.io.File;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

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

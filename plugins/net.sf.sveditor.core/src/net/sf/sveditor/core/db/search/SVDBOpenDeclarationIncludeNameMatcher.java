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

import java.util.regex.Pattern;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBOpenDeclarationIncludeNameMatcher extends
		SVDBFindDefaultNameMatcher {
	private static Pattern					fWinPathPattern;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}

	@Override
	public boolean match(SVDBItem it, String name) {
		if (it.getType() == SVDBItemType.File) {
			String norm_path = fWinPathPattern.matcher(it.getName()).replaceAll("/");
			
			return norm_path.endsWith(name); 
		} else {
			return super.match(it, name);
		}
	}
	
	

}

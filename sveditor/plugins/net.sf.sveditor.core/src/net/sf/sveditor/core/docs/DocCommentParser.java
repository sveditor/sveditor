/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class DocCommentParser implements IDocCommentParser {
	
	private static Pattern fIsDocCommentPattern ;
	
	static {
		fIsDocCommentPattern = Pattern.compile(
						"("
					+		"class"
					+   	"|task"
					+   	"|function"
					+   ")\\s*:\\s*(\\w+)",
			Pattern.CASE_INSENSITIVE) ;
	}

	public String isDocComment(String comment) {
		Matcher matcher = fIsDocCommentPattern.matcher(comment) ;
		if(matcher.find()) {
			return matcher.group(2) ;
		} else {
			return null ;
		}
	}

}

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


package net.sf.sveditor.core;

import java.io.File;
import java.util.regex.Pattern;

public class SVFileUtils {
	private static Pattern					fWinPathPattern;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	
	public static String getPathParent(String path) {
		path = new File(path).getParent();
		return fWinPathPattern.matcher(path).replaceAll("/");
	}
	
	public static String normalize(String path) {
		return fWinPathPattern.matcher(path).replaceAll("/");
	}
	

}

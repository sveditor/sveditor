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

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;

public class SVFileUtils {
	private static Pattern					fWinPathPattern;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	
	public static String getPathParent(String path) {
		String parent = new File(path).getParent();
		
		if (parent == null) {
			System.out.println("Failed to get parent of \"" + path + "\"");
			parent = path;
		}
		return fWinPathPattern.matcher(parent).replaceAll("/");
	}
	
	public static String normalize(String path) {
		path = fWinPathPattern.matcher(path).replaceAll("/");
		if (path.length() >= 3 && path.charAt(0) == '/' &&
				Character.isLetter(path.charAt(1)) &&
				path.charAt(2) == ':') {
			// If this is a windows path prefixed with '/', 
			// fix up:
			// /C:/foo => C:/foo
			path = path.substring(1);
		}
		return path;
	}
	
	public static IContainer getWorkspaceFolder(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IResource r = null;
		IProject  p = null;

		try {
			if ((r = root.getFolder(new Path(path))) != null && r.exists()) {
				return (IContainer)r;
			}
		} catch (IllegalArgumentException e) {
			// ignore, since this probably means we're looking at a project
		}
		
		// See if this is a project root
		String pname = path;
		if (pname.startsWith("/")) {
			pname = pname.substring(1);
		}
		if (pname.endsWith("/")) {
			pname = pname.substring(0, pname.length()-1);
		}
		for (IProject p_t : root.getProjects()) {
			if (p_t.getName().equals(pname)) {
				p = p_t;
				break;
			}
		}
		
		return p;
	}

}

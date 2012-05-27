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
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.security.MessageDigest;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;


public class SVFileUtils {
	private static Pattern					fWinPathPattern;
	public static boolean					fIsWinPlatform;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	
	public static String getPathParent(String path) {
		String parent = new File(path).getParent();
		
		if (parent == null) {
			parent = path;
		}
		return fWinPathPattern.matcher(parent).replaceAll("/");
	}

	public static String getPathLeaf(String path) {
		String leaf = new File(path).getName();
		
		return leaf;
	}

	public static String normalize(String path) {
		if (path.indexOf('\\') != -1) {
			path = fWinPathPattern.matcher(path).replaceAll("/");
			if (path.length() >= 3 && path.charAt(0) == '/' &&
					Character.isLetter(path.charAt(1)) &&
					path.charAt(2) == ':') {
				// If this is a windows path prefixed with '/', 
				// fix up:
				// /C:/foo => C:/foo
				path = path.substring(1);
			}
		}
		return path;
	}
	
	public static IContainer getWorkspaceFolder(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IResource r = null;
		IProject  p = null;
		
		path = normalize(path);

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
	
    private static String convertToHex(byte[] data) { 
        StringBuffer buf = new StringBuffer();
        for (int i = 0; i < data.length; i++) { 
            int halfbyte = (data[i] >>> 4) & 0x0F;
            int two_halfs = 0;
            do { 
                if ((0 <= halfbyte) && (halfbyte <= 9)) 
                    buf.append((char) ('0' + halfbyte));
                else 
                    buf.append((char) ('a' + (halfbyte - 10)));
                halfbyte = data[i] & 0x0F;
            } while(two_halfs++ < 1);
        } 
        return buf.toString();
    } 
 
    public static String computeMD5(String text) {
    	try {
    		MessageDigest md;
    		md = MessageDigest.getInstance("MD5");
    		byte[] md5hash = new byte[32];
    		md.update(text.getBytes("iso-8859-1"), 0, text.length());
    		md5hash = md.digest();
    		return convertToHex(md5hash);
    	} catch (Exception e) {
    		e.printStackTrace();
    	}
    	return "UNSUPPORTED";
    }
    
    public static void writeToFile(File file, String content) {
    	try {
    		PrintWriter out = new PrintWriter(new FileWriter(file.toString())) ;
    		out.print(content) ;
    		out.close();
    	} catch (IOException e){
    		e.printStackTrace();
    	}       	
    }
    
    public static void delete(File file) {
    	if (!file.exists()) {
    		return;
    	}
    	
    	if (file.isDirectory()) {
    		for (File f : file.listFiles()) {
    			delete(f);
    		}
    	}
    	file.delete();
    }
    
}

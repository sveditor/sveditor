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

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.security.MessageDigest;
import java.util.regex.Pattern;

import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;


public class SVFileUtils {
	private static Pattern					fWinPathPattern;
	public static boolean					fIsWinPlatform;
	private static boolean					fDebugEn;
	private static LogHandle				fLog;
	private static ILogLevelListener		fLogListener = new ILogLevelListener() {
		
		public void logLevelChanged(ILogHandle handle) {
			fDebugEn = handle.isEnabled();
		}
	};
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
		fLog = LogFactory.getLogHandle("SVFileUtils");
		fDebugEn = fLog.isEnabled();
		fLog.addLogLevelListener(fLogListener);
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
	
	public static IFile getWorkspaceFile(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IFile f = null;
		
		path = normalize(path);

		f = root.getFile(new Path(path));
		
		return f;
	}

	/**
	 * Attempts to map a filesystem path to a workspace one
	 * @param path
	 * @return
	 */
	public static IFile findWorkspaceFile(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		IFile f = root.getFileForLocation(new Path(path));
		
		return f;
	}
	
	/**
	 * Attempts to map a filesystem path to a workspace one
	 * @param path
	 * @return
	 */
	public static IContainer findWorkspaceFolder(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		IContainer c = root.getContainerForLocation(new Path(path));
		
		return c;
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
  
    /**
     * Resolves a path to its full path. Removes any 
     * @param path_orig
     * @param in_workspace_ok
     * @return
     */
	public static String resolvePath(
			String 					path_orig, 
			String					base_location,
			ISVDBFileSystemProvider	fs_provider,
			boolean 				in_workspace_ok) {
		String path = path_orig;
		String norm_path = null;

		if (fDebugEn) {
			fLog.debug("--> resolvePath: " + path_orig);
		}

		// relative to the base location or one of the include paths
		if (path.startsWith("..")) {
			if (fDebugEn) {
				fLog.debug("    path starts with ..");
			}
			if ((norm_path = resolveRelativePath(base_location, fs_provider, path)) == null) {
				/*
				for (String inc_path : fIndexCacheData.getIncludePaths()) {
					if (fDebugEn) {
						fLog.debug("    Check: " + inc_path + " ; " + path);
					}
					if ((norm_path = resolveRelativePath(inc_path, path)) != null) {
						break;
					}
				}
				 */
			} else {
				if (fDebugEn) {
					fLog.debug("norm_path=" + norm_path);
				}
			}
		} else {
			if (path.equals(".")) {
				path = base_location;
			} else if (path.startsWith(".")) {
				path = base_location + "/" + path.substring(2);
			} else {
				if (!fs_provider.fileExists(path) && !fs_provider.isDir(path)) {
					// See if this is an implicit path
					String imp_path = base_location + "/" + path;

					if (fs_provider.fileExists(imp_path) || fs_provider.isDir(imp_path)) {
						// This path is an implicit relative path that is
						// relative to the base directory
						path = imp_path;
					}
				}
			}
			norm_path = normalizePath(path);
		}
		
		if (norm_path != null && !norm_path.startsWith("${workspace_loc}") && in_workspace_ok) {
			IWorkspaceRoot ws_root = null;
			
			try {
				ws_root =ResourcesPlugin.getWorkspace().getRoot();
			} catch (IllegalStateException e) {}
		
			if (ws_root != null) {
				IFile file = ws_root.getFileForLocation(new Path(norm_path));
				if (file != null && file.exists()) {
					norm_path = "${workspace_loc}" + file.getFullPath().toOSString();
				} else {
					IContainer folder = ws_root.getContainerForLocation(new Path(norm_path));
					if (folder != null && folder.exists()) {
						norm_path = "${workspace_loc}" + folder.getFullPath().toOSString();
					}
				}
			}
		}
		
		norm_path = (norm_path != null) ? norm_path : path_orig;
		
		if (fDebugEn) {
			fLog.debug("<-- resolvePath: " + path_orig + " " + norm_path);
		}

		return norm_path;
	}

	private static String resolveRelativePath(
			String 						base_location,
			ISVDBFileSystemProvider		fs_provider,
			String 						path) {
		String ret = null;
		if (fDebugEn) {
			fLog.debug("--> resolveRelativePath: base=" + base_location + " path=" + path);
		}
		
		// path = getResolvedBaseLocationDir() + "/" + path;
		String norm_path = normalizePath(base_location + "/" + path);

		if (fDebugEn) {
			fLog.debug("    Checking normalizedPath: " + norm_path
					+ " ; ResolvedBaseLocation: " + base_location);
		}

		if (fs_provider.fileExists(norm_path) || fs_provider.isDir(norm_path)) {
			ret = norm_path;
		} else if (base_location.startsWith("${workspace_loc}")) {
			// This could be a reference outside the workspace. Check
			// whether we should reference this as a filesystem path
			// by computing the absolute path
			String base_loc = base_location;
			if (fDebugEn) {
				fLog.debug("Possible outside-workspace path: " + base_loc);
			}
			base_loc = base_loc.substring("${workspace_loc}".length());

			if (fDebugEn) {
				fLog.debug("    base_loc: " + base_loc);
			}

			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IContainer base_dir = null;
			try {
				base_dir = root.getFolder(new Path(base_loc));
			} catch (IllegalArgumentException e) {
			}

			if (base_dir == null) {
				if (base_loc.length() > 0) {
					base_dir = root.getProject(base_loc.substring(1));
				}
			}

			if (fDebugEn) {
				fLog.debug("base_dir=" + ((base_dir != null)?base_dir.getFullPath().toOSString():null));
			}

			if (base_dir != null && base_dir.exists()) {
				IPath base_dir_p = base_dir.getLocation();
				if (base_dir_p != null) {
					if (fDebugEn) {
						fLog.debug("Location of base_dir: " + base_dir_p.toOSString());
					}
					File path_f_t = new File(base_dir_p.toFile(), path);
					if (fDebugEn) {
						fLog.debug("Checking if path exists: " + path_f_t.getAbsolutePath() + " " + path_f_t.exists());
					}
					try {
						if (path_f_t.exists()) {
							if (fDebugEn) {
								fLog.debug("Path does exist outside the project: "
										+ path_f_t.getCanonicalPath());
							}
							norm_path = SVFileUtils.normalize(path_f_t
									.getCanonicalPath());
							ret = norm_path;
						}
					} catch (IOException e) {
						e.printStackTrace();
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("<-- resolveRelativePath: base=" + base_location + " path=" + path + " ret=" + ret);
		}
		return ret;
	}

	public static String normalizePath(String path) {
		StringBuilder ret = new StringBuilder();

		int i = path.length() - 1;
		int end;
		int skipCnt = 0;

		// First, skip any trailing '/'
		while (i >= 0 && (path.charAt(i) == '/' || path.charAt(i) == '\\')) {
			i--;
		}

		while (i >= 0) {
			// scan backwards find the next path element
			end = ret.length();

			while (i >= 0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
				ret.append(path.charAt(i));
				i--;
			}

			if (i != -1) {
				ret.append("/");
				i--;
			}

			if ((ret.length() - end) > 0) {
				String str = ret.substring(end, ret.length() - 1);
				if (str.equals("..")) {
					skipCnt++;
					// remove .. element
					ret.setLength(end);
				} else if (skipCnt > 0) {
					ret.setLength(end);
					skipCnt--;
				}
			}
		}

		return ret.reverse().toString();
	}    
	
	public static void copy(ByteArrayOutputStream in, File out) {
		byte tmp[] = new byte[1024*8];
		try {
			OutputStream out_s = new FileOutputStream(out);
			InputStream  in_s = new ByteArrayInputStream(in.toByteArray());
	
			int len;
			
			do {
				len = in_s.read(tmp, 0, tmp.length);
				if (len > 0) {
					out_s.write(tmp, 0, len);
				}
			} while (len > 0);
			
			out_s.close();
		} catch (IOException e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}

	public static void copy(ByteArrayOutputStream in, IFile out) {
		try {
			InputStream  in_s = new ByteArrayInputStream(in.toByteArray());

			if (out.exists()) {
				out.setContents(in_s, true, false, new NullProgressMonitor());
			} else {
				out.create(in_s, true, new NullProgressMonitor());
			}
		} catch (Exception e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}
	
	public static void copy(String in, IFile out) {
		try {
			InputStream  in_s = new StringInputStream(in);

			if (out.exists()) {
				out.setContents(in_s, true, false, new NullProgressMonitor());
			} else {
				out.create(in_s, true, new NullProgressMonitor());
			}
		} catch (Exception e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}

	public static void copy(String in, File out) {
		try {
			PrintStream ps = new PrintStream(out);
			ps.print(in);
			ps.close();
		} catch (Exception e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}
	
	public static void mkdir(IContainer c, String dir) {
		IFolder f = c.getFolder(new Path(dir));
		
		try {
			f.create(true, true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public static String readInput(InputStream in) {
		StringBuilder sb = new StringBuilder();
		byte tmp[] = new byte[1024];
		int len;
		
		try {
			while ((len = in.read(tmp, 0, tmp.length)) > 0) {
				sb.append(new String(tmp, 0, len));
			}
		} catch (IOException e) {
			
		}
		return sb.toString();
	}
	
	public static File getLocation(String path) {
		if (path.startsWith("${workspace_loc}")) {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			path = path.substring("${workspace_loc}".length());
			IResource rsrc = null;
		
			try {
				rsrc = root.getFile(new Path(path));
			} catch (IllegalArgumentException e) {}
			
			if (rsrc == null || !rsrc.exists()) {
				try {
					rsrc = root.getFolder(new Path(path));
				} catch (IllegalArgumentException e) {}
			}
		
			if (rsrc == null || !rsrc.exists()) {
				// See if this is a project
				String path_t = path;
				if (path_t.startsWith("/")) {
					path_t = path_t.substring(1);
				}
				
				try {
					rsrc = root.getProject(path_t);
				} catch (IllegalArgumentException e) {}
			}
			
			if (rsrc != null && rsrc.exists()) {
				return rsrc.getLocation().toFile();
			} else {
				return new File(path);
			}
		} else {
			return new File(path);
		}
	}
	
	public static void refresh(String path) {
		if (path.startsWith("${workspace_loc}")) {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			path = path.substring("${workspace_loc}".length());
			IResource rsrc = null;
		
			try {
				rsrc = root.getFile(new Path(path));
			} catch (IllegalArgumentException e) {}
			
			if (rsrc == null || !rsrc.exists()) {
				try {
					rsrc = root.getFolder(new Path(path));
				} catch (IllegalArgumentException e) {}
			}
		
			if (rsrc == null || !rsrc.exists()) {
				// See if this is a project
				String path_t = path;
				if (path_t.startsWith("/")) {
					path_t = path_t.substring(1);
				}
				
				try {
					rsrc = root.getProject(path_t);
				} catch (IllegalArgumentException e) {}
			}
			
			if (rsrc != null && rsrc.exists()) {
				try {
					rsrc.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
				} catch (CoreException e) {}
			}
		}
	}	
}

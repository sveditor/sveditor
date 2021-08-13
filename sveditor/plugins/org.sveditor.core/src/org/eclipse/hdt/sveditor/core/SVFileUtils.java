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


package org.eclipse.hdt.sveditor.core;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Reader;
import java.lang.reflect.Method;
import java.net.URI;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IPathVariableManager;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.IValueVariable;
import org.eclipse.core.variables.VariablesPlugin;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.ILogLevelListener;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;


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
	
	public static boolean isWin() {
		return fIsWinPlatform;
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
	
	public static String getPathExt(String path) {
		String leaf = getPathLeaf(path);
		int idx;
		
		if (leaf != null && (idx = leaf.lastIndexOf('.')) != -1) {
			return leaf.substring(idx+1);
		} else {
			return null;
		}
	}
	
	public static String getPathFirstElem(String path) {
		String first = path;
		int idx;
		
		if ((idx = path.indexOf('/', 1)) != -1) { // avoid leading '/'
			int first_idx = path.indexOf('/');
		
			if (first_idx != -1) {
				if (first_idx != idx) {
					// There was a leading '/'
					first = path.substring(1, idx);
				} else {
					// We caught the first '/' with our initial search.
					// This happens with paths like ./foo
					if (path.charAt(idx-1) == '.') {
						// Yep
						int next_idx = path.indexOf('/', idx+1);
					
						if (next_idx != -1) {
							// up to there
							first = path.substring(idx+1, next_idx);
						} else {
							// Take the remainder of the string
							first = path.substring(idx+1);
						}
					} else {
						// No, this is probably a path like: foo/bar.svh
						first = path.substring(0, idx);
					}
				}
			} else {
				// There was no leading '/'
				first = path.substring(0, idx);
			}
		} else if ((idx = path.indexOf('\\', 1)) != -1) {
			if (path.length() > 0 && path.charAt(0) == '\\') {
				first = path.substring(1, idx);
			} else {
				first = path.substring(0, idx);
			}
		}
		
		return first;
	}
	
	public static List<String> splitPath(String path) {
		List<String> ret = new ArrayList<String>();
		int idx = 0;
		
	
		while (idx < path.length()) {
			// Skip separators
			while (idx < path.length() && path.charAt(idx) == '/') {
				idx++;
			}
	
			// Build name
			int name_start=idx;
			while (idx < path.length() && !(path.charAt(idx) == '/')) {
				idx++;
			}
	
			ret.add(path.substring(name_start, idx));
		}
	
		return ret;
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

	public static IResource getWorkspaceResource(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IResource r = null;
		IProject  p = null;
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
		}
		
		path = normalize(path);
		
		try {
			if ((r = root.getFolder(new Path(path))) != null && r.exists()) {
				return r;
			} else if ((r = root.getFile(new Path(path))) != null && r.exists()) {
				return r;
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

		try {
			f = root.getFile(new Path(path));
		} catch (IllegalArgumentException e) {
			// Ignore -- likely we asked for an invalid path
		}
		
		return f;
	}

	/**
	 * Resolves the specified path to its filesystem location
	 * 
	 * @param path
	 * @return
	 */
	public static File getFile(String path) {
		
		if (path.startsWith("${workspace_loc}")) {
			String ws_path = path.substring("${workspace_loc}".length());
			
			IFile file = getWorkspaceFile(ws_path);
			
			if (file != null && file.exists()) {
				return file.getLocation().toFile();
			}
			
			IContainer folder = getWorkspaceFolder(ws_path);
			
			if (folder != null && folder.exists()) {
				return folder.getLocation().toFile();
			}
			
			return new File(path);
		} else {
			return new File(path);
		}
	}

	/**
	 * Attempts to map a filesystem path to a workspace one
	 * @param path
	 * @return
	 */
	public static IFile findWorkspaceFile(String path) {
		IFile f = null;
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			try {
				f = root.getFile(new Path(path));
			} catch (IllegalStateException e) {
				// Happens when the workspace is closed
			} catch (IllegalArgumentException e) {
				// Happens when we're called with a /project path
			}
		} else {
			try {
				f = root.getFileForLocation(new Path(path));
				
				if (f == null) {
					// getFileForLocation only looks at resources actually in the workspace
					// findFilesForLocationURI searches linked resources as well
					IFile files[] = root.findFilesForLocationURI((new File(path)).toURI());
					
					if (files != null && files.length > 0) {
						f = files[0];
					}
				}
			} catch (IllegalStateException e) {
				// Happens when the workspace is closed
			}
		}

		
		return f;
	}

	/**
	 * Attempts to map a filesystem path to a workspace one
	 * @param path
	 * @return
	 */
	public static IFile[] findWorkspaceFiles(String path) {
		IFile f[] = null;
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			try {
				IFile tf = root.getFile(new Path(path));
				
				if (tf != null) {
					f = new IFile[] {tf};
				}
			} catch (IllegalStateException e) {
				// Happens when the workspace is closed
			}
		} else {
			try {
				f = root.findFilesForLocationURI((new File(path)).toURI());
			} catch (IllegalStateException e) {
				// Happens when the workspace is closed
			}
		}
		
		return f;
	}
	
	/**
	 * Attempts to map a filesystem path to a workspace one
	 * @param path
	 * @return
	 */
	public static IContainer findWorkspaceFolder(String path) {
		IContainer c = null;
		try {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
			c = root.getContainerForLocation(new Path(path));
			
			if (c == null) {
				// Try the longer route
				IContainer c_l[] = root.findContainersForLocationURI((new File(path)).toURI());
				
				if (c_l != null && c_l.length > 0) {
					c = c_l[0];
				}
			}
		} catch (IllegalStateException e) {
			// Happens when the workspace is closed
		}
		
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
    
    public static void delete(IFile file) {
    	try {
    		file.delete(true, new NullProgressMonitor());
    	} catch (CoreException e) {
    		e.printStackTrace();
    	}
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
				// First, check whether the file exists inside the base location
				// Directly checking the unresolved path can result in strangeness
				// when a relative path with the same name exists in the working directory
				String try_path = base_location + "/" + path;
				if (fs_provider.fileExists(try_path) || fs_provider.isDir(try_path)) {
					path = try_path;
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
		norm_path = normalizePath(norm_path);
		
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

	public static IFile copy(ByteArrayOutputStream in, IFile out) {
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
		return out;
	}
	
	public static IFile copy(String in, IFile out) {
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
		
		return out;
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
	
	public static IFolder mkdir(IContainer c, String dir) {
		IFolder f = c.getFolder(new Path(dir));
		
		try {
			f.create(true, true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		return f;
	}
	
	public static String readInput(File path) {
		try {
			FileInputStream in = new FileInputStream(path);
			String ret = readInput(in);
			in.close();
		
			return ret;
		} catch (IOException e) {
			return null;
		}
	}
	
	public static List<String> readInputLines(InputStream in) {
		List<String> ret = new ArrayList<String>();
		BufferedReader rdr = new BufferedReader(new InputStreamReader(in));
		String line;
		
		try {
			while ((line = rdr.readLine()) != null) {
				ret.add(line);
			}
		} catch (IOException e) { }
		
		return ret;
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
	
	public static String expandVars(String path, String projectname, boolean in_workspace_ok) {

		boolean workspace_prefix = path.startsWith("${workspace_loc}");
		String exp_path = path;
		
		if (workspace_prefix) {
			exp_path = exp_path.substring("${workspace_loc}".length());
		}
		
		/*
		 * Hackish support for project relative paths.
		 *   There's quite a bit of special processing throughout
		 *   the plugin for worspace_loc used in paths
		 *   with no similar processing for project_loc. Rather than
		 *   further complicating all the worspace_loc processing it
		 *   was decided to piggyback on it by converting the 
		 *   project_loc into a workspace_loc.
		 * 
		 */
		boolean project_prefix = path.startsWith("${project_loc}") && (projectname != null);
		if (project_prefix) {
			exp_path = "/" + projectname + exp_path.substring("${project_loc}".length());
			workspace_prefix = true;
		}
		
		IWorkspace workspace = null;
		try {
			workspace = ResourcesPlugin.getWorkspace();
		} catch (IllegalStateException e) {}

		IPathVariableManager pvm = null;
		IProject project = null;
		IStringVariableManager svm = null;
		if (workspace != null) {
			pvm = ResourcesPlugin.getWorkspace().getPathVariableManager();
			
			if (projectname != null) {
				project = workspace.getRoot().getProject(projectname);
			}
			svm = (VariablesPlugin.getDefault() != null)?VariablesPlugin.getDefault().getStringVariableManager():null;
		}
		 
		StringBuilder sb = new StringBuilder(exp_path);
		StringBuilder tmp = new StringBuilder();

		int found_var = 1;
		
		while (found_var == 1)  {
			int idx = 0;
			found_var = 0;
	
			while (idx < sb.length()) {
				if (sb.charAt(idx) == '$') {
					tmp.setLength(0);
	
					int start = idx, end;
					String key, val=null;
					idx++;
					if (sb.charAt(idx) == '{') {
						idx++;
	
						while (idx < sb.length() && sb.charAt(idx) != '}') {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						if (idx < sb.length()) {
							end = ++idx;
						} else {
							end = idx;
						}
					} else {
						while (idx < sb.length() && 
								sb.charAt(idx) != '/' && !Character.isWhitespace(sb.charAt(idx))) {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						end = idx;
					}
	
					key = tmp.toString();
					// Priority order is: 
					// - Check Linked Resources
					// - Check environment
					// - Check Variables
					val = null;

					// Check for project path variables
					// These are typically set in  
					// Project Properties > Resource > Linked Resources > Path Variables 
					if (val == null && project != null) {
						IPath p = null;
						// Eclipse 3.5.2
						// PathVariableManager was added in 3.6.2. We still want
						// to support 3.5.2, so this is the workaround for the following code:
						// IPathVariableManager ppvm = project.getPathVariableManager();
						try {
							Class<? extends IProject> c = project.getClass();
							Method get_path_variable_manager = c.getMethod("getPathVariableManager");
							
							if (get_path_variable_manager != null) {
								pvm = (IPathVariableManager)get_path_variable_manager.invoke(project);
								p = pvm.getValue(key);
							}
						} catch (Exception e) {}
						if (p != null) {
							val = p.toString();
							if (val.matches("^/[a-zA-Z]:.*"))  {
								// For some reason PROJECT_LOC will return:
								// /L:\somepath
								// instead of L:\somepath
								// This seems to be pretty normal with "file" types of URI's, this code strips the leading 
								val = val.replaceFirst("/", "");
							}
						}
					}
					
					// Eclipse Project Variables
					if (val == null && pvm != null) {
//						IPath p = pvm.getValue(key);
						URI p = pvm.getURIValue(key);
						if (p != null) {
//							val = p.toString();
							val = p.getPath();
						}
					}
					// Environment variables
					if (val == null) {
						val = SVCorePlugin.getenv(key);
					}
					// SVE Variables
					if (val == null && svm != null) {
						IValueVariable v = svm.getValueVariable(key);
						if (v != null) {
							val = v.getValue();
						}
					}
					if (val != null) {
						found_var = 1;
						sb.replace(start, end, val);
						break;	// need to break because our string has been changed, start again
					}
				} else {
					idx++;
				}
			}
		}
			
		exp_path = sb.toString();
			
		// VariablesPlugin.getDefault().getStringVariableManager().getValueVariable(name)
	
			
		// Allow for outside-Eclipse run -- primarily for profiling
		if (VariablesPlugin.getDefault() != null) {
			IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();

			try {
				exp_path = mgr.performStringSubstitution(exp_path);
			} catch (CoreException e) {
//				System.out.println("Expansion failure: " + path + "; " + project);
//				e.printStackTrace();
			}
		}
		
		// It's possible that the expanded path is actually within 
		// the workspace, even though the path is an absolute path.
		// See if this is the case
		if (!workspace_prefix && in_workspace_ok) {
			IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = ws_root.getFileForLocation(new Path(exp_path));
			if (file != null && file.exists()) {
				workspace_prefix = true;
				exp_path = file.getFullPath().toOSString();
			}
		}
		
		if (workspace_prefix) {
			exp_path = "${workspace_loc}" + exp_path;
		}
		
		return exp_path;
	}

}

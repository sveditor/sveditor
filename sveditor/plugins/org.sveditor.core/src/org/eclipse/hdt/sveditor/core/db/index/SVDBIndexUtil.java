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


package org.eclipse.hdt.sveditor.core.db.index;

import java.io.File;
import java.lang.reflect.Method;
import java.net.URI;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IPathVariableManager;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.IValueVariable;
import org.eclipse.core.variables.VariablesPlugin;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.search.SVDBSearchResult;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;



public class SVDBIndexUtil {
	
	private static LogHandle		fLog = LogFactory.getLogHandle("SVDBIndexUtil");
	
	/**
	 * Gets the SVDB file associated with a given file
	 * 
	 * @param file
	 * @return
	 */
	public static SVDBFile findIndexFile(IFile file) {
		SVDBFile ret = null;
		
		// First, find the project that manages this file
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = p_mgr.getProjectData(file.getProject());
		
		if (pd != null) {
			List<SVDBSearchResult<SVDBFile>> result = 
					pd.getProjectIndexMgr().findFile(
							"${workspace_loc}" + file.getFullPath());
			if (result.size() > 0) {
				ret = result.get(0).getItem();
			}
		}
		
		return ret;
	}
	
	/**
	 * Gets the SVDB Iterator file associated with a given file
	 * 
	 * @param file
	 * @return
	 */
	public static ISVDBIndexIterator findIndexIterator(IFile file) {
		ISVDBIndexIterator ret = null;
		
		// First, find the project that manages this file
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = p_mgr.getProjectData(file.getProject());
		ret = pd.getProjectIndexMgr();
		
//		if (pd != null) {
//			List<SVDBSearchResult<SVDBFile>> result = 
//					pd.getProjectIndexMgr().findFile(
//							"${workspace_loc}" + file.getFullPath());
//			if (result.size() > 0) {
//				ret = result.get(0).getItem();
//			}
//		}
		
		return ret;
	}
	
	/**
	 * findIndexFile()
	 * 
	 * @param path
	 * @param project
	 * @param create_shadow
	 * @return
	 */
	public static Tuple<ISVDBIndex, SVDBIndexCollection> findIndexFile(String path, String project, boolean create_shadow) {
		ISVDBIndex 				index     = null;
		SVDBIndexCollection	index_mgr = null;
		IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot();

		// Sort the project list so we check the active project's
		// index first
		List<IProject> projects = new ArrayList<IProject>();
		for (IProject p : ws_root.getProjects()) {
			if (project != null && p.getName().equals(project)) {
				projects.add(0, p);
			} else {
				projects.add(p);
			}
		}
		
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		// First, search without looking at shadow indexes
		for (IProject p : projects) {
			// Ignore projects that are closed
			if (!p.isOpen()) {
				continue;
			}
			SVDBProjectData pdata = p_mgr.getProjectData(p);
			List<ISVDBIndex> result = pdata.getProjectIndexMgr().findManagingIndex(path);
			if (result.size() > 0) {
				index = result.get(0);
				fLog.debug("File \"" + path + "\" is in index " + 
						index.getBaseLocation() + " in project " + pdata.getName());
				index_mgr = pdata.getProjectIndexMgr();
				break;
			} /* else if (path.startsWith("${workspace_loc}")) {
				// Try searching with the filesystem path in case the user
				// has specified the index in terms of the filesystem
				String ws_path = path.substring("${workspace_loc}".length());
				IFile f = ws_root.getFile(new Path(ws_path));
				
				if (f != null && f.exists()) {
					File fs_file = f.getLocation().toFile();
					result = pdata.getProjectIndexMgr().findPreProcFile(fs_file.getAbsolutePath(), false);
					if (result.size() > 0) {
						index = result.get(0).getIndex();
						fLog.debug("File \"" + path + "\" is in index " + 
								index.getBaseLocation() + " in project " + pdata.getName());
						index_mgr = pdata.getProjectIndexMgr();
						break;
					}
				}
			} */
		}
		
		if (index == null) {
			// Now, search shadow indexes as well
			for (IProject p : projects) {
				if (!p.isOpen()) {
					continue;
				}
				
				SVDBProjectData pdata = p_mgr.getProjectData(p);
				List<SVDBSearchResult<SVDBFile>> result = pdata.getProjectIndexMgr().findPreProcFile(path, true);
				if (result.size() > 0) {
					index = result.get(0).getIndex();
					index_mgr = pdata.getProjectIndexMgr();
					fLog.debug("File \"" + path + "\" is in existing shadow index " + 
							index.getBaseLocation() + " in project " + pdata.getName());
					break;
				}
			}
		}
		
		if (index == null) {
			// Finally, check the global shadow indexes
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			for (ISVDBIndex idx_t : rgy.getProjectIndexList(SVDBIndexRegistry.GLOBAL_PROJECT)) {
				if (idx_t.findPreProcFile(path) != null) {
					index = idx_t;
					index_mgr = rgy.getGlobalIndexMgr();
				}
			}
		}

		if (index != null) {
			return new Tuple<ISVDBIndex, SVDBIndexCollection>(index, index_mgr);
		} else {
			return null;
		}
	}

	public static Tuple<ISVDBIndex, SVDBIndexCollection> findArgFileIndex(String path, String project) {
		ISVDBIndex 				index     = null;
		SVDBIndexCollection	index_mgr = null;
		IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot();

		// Sort the project list so we check the active project's
		// index first
		List<IProject> projects = new ArrayList<IProject>();
		for (IProject p : ws_root.getProjects()) {
			if (project != null && p.getName().equals(project)) {
				projects.add(0, p);
			} else {
				projects.add(p);
			}
		}
		
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();

		for (IProject p : projects) {
			// Ignore projects that are closed
			if (!p.isOpen()) {
				continue;
			}
			SVDBProjectData pdata = p_mgr.getProjectData(p);
			List<SVDBSearchResult<SVDBFile>> result = pdata.getProjectIndexMgr().findFile(path, true);
			if (result.size() > 0) {
				index = result.get(0).getIndex();
				fLog.debug("ArgFile \"" + path + "\" is in index " + 
						index.getBaseLocation() + " in project " + pdata.getName());
				index_mgr = pdata.getProjectIndexMgr();
				break;
			} else if (path.startsWith("${workspace_loc}")) {
				// Try searching with the filesystem path in case the user
				// has specified the index in terms of the filesystem
				String ws_path = path.substring("${workspace_loc}".length());
				IFile f = ws_root.getFile(new Path(ws_path));
				
				if (f != null && f.exists()) {
					File fs_file = f.getLocation().toFile();
					result = pdata.getProjectIndexMgr().findFile(fs_file.getAbsolutePath(), true);
					if (result.size() > 0) {
						index = result.get(0).getIndex();
						fLog.debug("ArgFile \"" + path + "\" is in index " + 
								index.getBaseLocation() + " in project " + pdata.getName());
						index_mgr = pdata.getProjectIndexMgr();
						break;
					}
				}
			}
		}
		
		if (index != null) {
			return new Tuple<ISVDBIndex, SVDBIndexCollection>(index, index_mgr);
		} else {
			return null;
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
		boolean project_prefix = path.startsWith("${project_loc}");
		if (project_prefix) {
			exp_path = projectname + exp_path.substring("${project_loc}".length());
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


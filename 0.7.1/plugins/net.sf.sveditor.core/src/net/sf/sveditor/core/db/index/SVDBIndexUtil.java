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


package net.sf.sveditor.core.db.index;

import java.net.URI;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IPathVariableManager;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.IValueVariable;
import org.eclipse.core.variables.VariablesPlugin;


public class SVDBIndexUtil {
	
	private static LogHandle		fLog = LogFactory.getLogHandle("SVDBIndexUtil");
	
	/**
	 * findIndexFile()
	 * 
	 * @param path
	 * @param project
	 * @param create_shadow
	 * @return
	 */
	public static Tuple<ISVDBIndex, SVDBIndexCollectionMgr> findIndexFile(String path, String project, boolean create_shadow) {
		ISVDBIndex 				index     = null;
		SVDBIndexCollectionMgr	index_mgr = null;
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
			List<SVDBSearchResult<SVDBFile>> result = pdata.getProjectIndexMgr().findPreProcFile(path, false);
			if (result.size() > 0) {
				index = result.get(0).getIndex();
				fLog.debug("File \"" + path + "\" is in index " + 
						index.getBaseLocation() + " in project " + pdata.getName());
				index_mgr = pdata.getProjectIndexMgr();
				break;
			}
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

		if (index == null && create_shadow) {
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			
			fLog.debug("Create a shadow index for \"" + path + "\"");
			if (project != null) {
				SVDBProjectData   pdata = p_mgr.getProjectData(projects.get(0));
			
				index_mgr = pdata.getProjectIndexMgr();
			} else {
				index_mgr = rgy.getGlobalIndexMgr();
				project = SVDBIndexRegistry.GLOBAL_PROJECT;
			}
			
			SVFileSet fs = new SVFileSet(SVFileUtils.getPathParent(path));

			// Remove the depth-searching portion from all patterns
			String dflt_include = SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes();
			dflt_include = dflt_include.replace("**/", "");
			String dflt_exclude = SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes();
			dflt_exclude = dflt_exclude.replace("**/", "");
			fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(dflt_include));
			fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(dflt_exclude));
			
			Map<String, Object> config = new HashMap<String, Object>();
			config.put(SVDBSourceCollectionIndexFactory.FILESET, fs);
			
			
			index = rgy.findCreateIndex(new NullProgressMonitor(), project,
					SVFileUtils.getPathParent(path),
					SVDBSourceCollectionIndexFactory.TYPE, config);
			index_mgr.addShadowIndex(index.getBaseLocation(), index);
		}
		
		if (index != null) {
			return new Tuple<ISVDBIndex, SVDBIndexCollectionMgr>(index, index_mgr);
		} else {
			return null;
		}
	}

	public static String expandVars(String path, String projectname) {

		boolean workspace_prefix = path.startsWith("${workspace_loc}");
		String exp_path = path;
		
		if (workspace_prefix) {
			exp_path = exp_path.substring("${workspace_loc}".length());
		}

		IPathVariableManager pvm = ResourcesPlugin.getWorkspace().getPathVariableManager();
		IProject project = null;
		
		if (projectname != null) {
			project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectname);
		}
		 
		IStringVariableManager svm = (VariablesPlugin.getDefault() != null)?VariablesPlugin.getDefault().getStringVariableManager():null;
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
						IPathVariableManager ppvm = project.getPathVariableManager();
						URI p = ppvm.getURIValue(key);
						if (p != null) {
							val = p.getPath();
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
					if (val == null) {
						URI p = pvm.getURIValue(key);
						if (p != null) {
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
				e.printStackTrace();
			}
		}
		
		
		if (workspace_prefix) {
			exp_path = "${workspace_loc}" + exp_path;
		}
		
		return exp_path;
	}
}


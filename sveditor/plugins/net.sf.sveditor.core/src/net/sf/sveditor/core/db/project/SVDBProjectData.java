/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.project;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.ISVDBProjectRefProvider;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBProjectData implements ISVDBProjectRefProvider {
	private IProject								fProject;
	private SVProjectFileWrapper 					fFileWrapper;
	private boolean									fHaveDotSvProject;
	private SVDBIndexCollection						fIndexCollection;
	private String									fProjectName;
	private LogHandle								fLog;
	private List<ISVDBProjectSettingsListener>		fListeners;

	public SVDBProjectData(IProject	project) {
//		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		fProject = project;
		fLog = LogFactory.getLogHandle("SVDBProjectData");
		fListeners = new ArrayList<ISVDBProjectSettingsListener>();
		fProjectName    = project.getName();
		
		fLog.debug("Create SVDBProjectData for \"" + project.getName() + "\"");
		
		init();
	}
	
	public synchronized void refresh() {
		IFile svproject = fProject.getFile(".svproject");
		
		if (!fHaveDotSvProject && svproject.exists()) {
			init();
		}
	}
	
	public void init() {
		IFile svproject = fProject.getFile(".svproject");
		SVProjectFileWrapper wrapper;
		
		if (svproject.exists()) {
			fLog.debug(".svproject exists");
			wrapper = readProjectFile(svproject);
			fHaveDotSvProject = true;
		} else {
			// Create defaults
//			Exception e = null;
//			try {
//				throw new Exception();
//			} catch (Exception ex) {
//				e = ex;
//			}
			fLog.debug(".svproject does not exist");
			wrapper = new SVProjectFileWrapper();
			SVDBProjectManager.setupDefaultProjectFile(wrapper);
			fHaveDotSvProject = false;
		}

		// Initialize to null, so initial setup is performed
		fFileWrapper = null;
		setProjectFileWrapper(wrapper, false);
	}
	
	public IProject getProject() {
		return fProject;
	}
	
	public boolean haveDotSvProject() {
		return fHaveDotSvProject;
	}
	
	public SVDBIndexCollection resolveProjectRef(String path) {
		IWorkspace ws = ResourcesPlugin.getWorkspace();
		IWorkspaceRoot root = ws.getRoot();
		SVDBIndexCollection mgr = null;
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr(); 
		
		IProject p = root.getProject(path);
		if (p != null) {
			SVDBProjectData p_data = p_mgr.getProjectData(p);
			if (p_data != null) {
				mgr = p_data.getProjectIndexMgr();
			}
		}
		
		return mgr;
	}

	public String getName() {
		return fProjectName;
	}
	
	public void addProjectSettingsListener(ISVDBProjectSettingsListener l) {
		synchronized (fListeners) {
			fListeners.add(l);
		}
	}
	
	public void removeProjectSettingsListener(ISVDBProjectSettingsListener l) {
		synchronized (fListeners) { 
			fListeners.remove(l);
		}
	}

	public synchronized SVDBIndexCollection getProjectIndexMgr() {
		if (fIndexCollection == null) {
			fIndexCollection = createProjectIndex();
		}
		
		return fIndexCollection;
	}
	
	private SVProjectFileWrapper readProjectFile(IFile svproject) {
		SVProjectFileWrapper wrapper = null;

		for (int i=0; i<2; i++) {
			try {
				if (svproject.exists()) {
					InputStream in = svproject.getContents();
					wrapper = new SVProjectFileWrapper(in);
				}
				break;
			} catch (Exception e) {
				if (e instanceof CoreException) {
					try {
						svproject.refreshLocal(IResource.DEPTH_ZERO, new NullProgressMonitor());
					} catch (CoreException ex) {}
				}
				fLog.debug("Failed to read .svproject", e);
			}
		}
	
		return wrapper;
	}

	public void refreshProjectFile() {
		IFile svproject = fProject.getFile(".svproject");
		SVProjectFileWrapper wrapper = null;
		
		if (svproject.exists()) {
			wrapper = readProjectFile(fProject.getFile(".svproject"));
		}
		
		if (wrapper != null) {
			fFileWrapper = wrapper;
		}
	}

	public SVProjectFileWrapper getProjectFileWrapper() {
		// Ensure we have the most up-to-date information
		refreshProjectFile();
		
		return fFileWrapper;
	}
	
	public synchronized void setProjectFileWrapper(SVProjectFileWrapper w) {
		setProjectFileWrapper(w, true);
	}

	public synchronized void setProjectFileWrapper(SVProjectFileWrapper w, boolean set_contents) {
		boolean refresh = set_contents;
		
		fLog.debug("setProjectFileWrapper set_contents=" + set_contents);
		for (SVDBPath path : w.getArgFilePaths()) {
			fLog.debug("  Path: " + path.getPath());
		}
		
		if (fFileWrapper == null || !fFileWrapper.equals(w)) {
			// Need to refresh
			fLog.debug("need to refresh");
			refresh = true;
		} else {
			fLog.debug("no need to refresh");
		}
		
		
		// Only write settings to the filesystem
		// if they are non-default values
		if (set_contents) {
			SVProjectFileWrapper default_settings = new SVProjectFileWrapper();
			SVDBProjectManager.setupDefaultProjectFile(default_settings);
		
			// Do write-back settings if both the new
			// settings and the current settings are
			// equal to the default
			if (default_settings.equals(w) && 
					default_settings.equals(fFileWrapper)) {
				set_contents = false;
			}
		}

		fFileWrapper = w;
		
		if (set_contents) {
			try {
				IFile file = fProject.getFile(".svproject");
				
// MSB:				file.refreshLocal(IResource.DEPTH_ONE, null);

				ByteArrayOutputStream out = new ByteArrayOutputStream();
				fFileWrapper.toStream(out);
				
				if (file.exists()) {
					file.setContents(new ByteArrayInputStream(
							out.toByteArray()),	true, true, null);
				} else {
					file.create(new ByteArrayInputStream(
							out.toByteArray()), true, null);
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		// Pull in references from project
		if (fProject != null) {
			IProject refs[] = null;
			try {
				refs = fProject.getReferencedProjects();
			} catch (CoreException e) {}
			
			if (refs == null) {
				refs = new IProject[0];
			}
			
			boolean set_paths = false;
			if (refs.length != w.getProjectRefs().size()) {
				set_paths = true;
			} else {
				for (int i=0; i<refs.length; i++) {
					SVDBPath p = new SVDBPath(refs[i].getName());
					if (!w.getProjectRefs().contains(p)) {
						set_paths = true;
						break;
					}
				}
			}
			
			if (set_paths) {
				refresh = true;
				w.getProjectRefs().clear();
				for (int i=0; i<refs.length; i++) {
					w.addProjectRef(refs[i].getName());
				}
			}
		}
		
		if (refresh || fIndexCollection == null) {
			if (fIndexCollection == null) {
				fIndexCollection = createProjectIndex();
			} else {
				setProjectPaths(fIndexCollection, fFileWrapper, refresh);
			}
		}
	}
	
	/**
	 * Creates the index for the project based on the paths registered
	 * in the project data
	 * 
	 * @return
	 */
	private SVDBIndexCollection createProjectIndex() {
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		SVDBIndexCollection ret = new SVDBIndexCollection(rgy.getIndexCollectionMgr(), fProjectName);
		SVProjectFileWrapper fw = getProjectFileWrapper();
		
		setProjectPaths(ret, fw, false);

		return ret;
	}
	
	private void setProjectPaths(
			SVDBIndexCollection 		sc,
			SVProjectFileWrapper		fw,
			boolean						refresh) {
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		Map<String, String> define_map = new HashMap<String, String>();
		SVDBIndexConfig args = new SVDBIndexConfig();
		
		for (Tuple<String, String> def : fw.getGlobalDefines()) {
			if (define_map.containsKey(def.first())) {
				define_map.remove(def.first());
			}
			define_map.put(def.first(), def.second());
		}
		
		sc.clear();
		sc.setProjectRefProvider(this);

		// Add project references
		for (SVDBPath pr : fw.getProjectRefs()) {
			sc.addProjectRef(pr.getPath());
		}

		// Add enabled plugin paths
		for (SVDBPath path : fw.getPluginPaths()) {
			ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				SVDBIndexRegistry.GLOBAL_PROJECT, path.getPath(), 
				SVDBPluginLibIndexFactory.TYPE, null);
			
			if (index != null) {
				sc.addPluginLibrary(index);
			} else {
				fLog.error(
						"failed to create library index \"" +
						path.getPath() + "\"");
			}
		}
		
//		args.clear();
//		args.put(ISVDBIndexFactory.KEY_GlobalDefineMap, define_map);

		// Add argument-file paths
		args.clear();
		args.put(ISVDBIndexFactory.KEY_GlobalDefineMap, define_map);
		for (SVDBPath path : fw.getArgFilePaths()) {
			ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
					fProjectName, expandPath(path.getPath()),
					SVDBArgFileIndexFactory.TYPE, args);
			
			if (index != null) {
				sc.addLibraryPath(index);
			} else {
				fLog.error(
						"failed to create arg-file index \"" +
						path.getPath() + "\"");
			}
		}
		
		// Clear out any project indexes that aren't being used
		List<ISVDBIndex> active_indexes = sc.getIndexList();
		List<ISVDBIndex> project_indexes = rgy.getProjectIndexList(fProjectName);
		for (ISVDBIndex i : active_indexes) {
			project_indexes.remove(i);
		}
		
		// Remove leftover indexes
		for (ISVDBIndex i : project_indexes) {
			rgy.disposeIndex(i, "Removing leftover project indexes");
		}
		
		// Push defines to all indexes. This may cause index rebuild
		for (ISVDBIndex index : rgy.getProjectIndexList(fProjectName)) {
			for (Tuple<String, String> def : fw.getGlobalDefines()) {
				index.setGlobalDefine(def.first(), def.second());
			}
		}
		
		// Project settings have changed, so notify listeners
		synchronized (fListeners) {
			for (ISVDBProjectSettingsListener l : fListeners) {
				l.projectSettingsChanged(this);
			}
		}
		
		// Also notify global listeners
		if (refresh) {
			SVCorePlugin.getDefault().getProjMgr().projectSettingsChanged(this);
		}
	}
	
	private String expandPath(String path) {
		int idx;
		
		while ((idx = path.indexOf("${project_loc}")) != -1) {
			if (idx == 0) {
				path = "${workspace_loc}/" + fProjectName + 
						path.substring(idx+"${project_loc}".length());
			} else {
				path = path.substring(0, idx) + "${workspace_loc}/" + fProjectName + 
						path.substring(idx+"${project_loc}".length());
			}
		}
		
		return path;
	}
	
	public boolean equals(Object other) {
		if (other instanceof SVDBProjectData) {
			SVDBProjectData o = (SVDBProjectData)other;
			boolean eq = true;
			
			eq &= o.fProjectName.equals(fProjectName);
			eq &= o.fFileWrapper.equals(fFileWrapper);
		
			return eq;
		} else {
			return false;
		}
	}
}

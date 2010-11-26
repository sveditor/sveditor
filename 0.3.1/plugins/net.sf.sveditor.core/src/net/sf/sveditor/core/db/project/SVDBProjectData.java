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
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.index.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;

public class SVDBProjectData {
	private IPath 									fSVProjFilePath;
	private SVProjectFileWrapper 					fFileWrapper;
	private SVDBIndexCollectionMgr					fIndexCollection;
	private String									fProjectName;
	private LogHandle								fLog;
	private List<ISVDBProjectSettingsListener>		fListeners;

	public SVDBProjectData(
			String						project_name,
			SVProjectFileWrapper 		wrapper, 
			IPath 						projfile_path) {
		fLog = LogFactory.getLogHandle("SVDBProjectData");
		fListeners = new ArrayList<ISVDBProjectSettingsListener>();
		fProjectName    = project_name;
		fSVProjFilePath = projfile_path;
		
		fIndexCollection = new SVDBIndexCollectionMgr(project_name);
		
		fFileWrapper = null;
		setProjectFileWrapper(wrapper, false);
	}
	
	public String getName() {
		return fProjectName;
	}
	
	public void addProjectSettingsListener(ISVDBProjectSettingsListener l) {
		fListeners.add(l);
	}
	
	public void removeProjectSettingsListener(ISVDBProjectSettingsListener l) {
		fListeners.remove(l);
	}

	public synchronized SVDBIndexCollectionMgr getProjectIndexMgr() {
		if (fIndexCollection == null) {
			fIndexCollection = createProjectIndex();
		}
		
		return fIndexCollection;
	}

	public void refreshProjectFile() {
		try {
			IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(
					fSVProjFilePath);
			InputStream in = file.getContents();

			fFileWrapper = new SVProjectFileWrapper(in);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public SVProjectFileWrapper getProjectFileWrapper() {
		return fFileWrapper;
	}
	
	public synchronized void setProjectFileWrapper(SVProjectFileWrapper w) {
		setProjectFileWrapper(w, true);
	}

	public synchronized void setProjectFileWrapper(SVProjectFileWrapper w, boolean set_contents) {
		boolean refresh = false;
		
		if (fFileWrapper == null || !fFileWrapper.equals(w)) {
			// Need to refresh
			fLog.debug("need to refresh");
			refresh = true;
		} else {
			fLog.debug("no need to refresh");
		}
		
		fFileWrapper = w;
		
		if (set_contents) {
			try {
				IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(
						fSVProjFilePath);

				file.refreshLocal(IResource.DEPTH_ONE, null);

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
		
		if (refresh && fIndexCollection != null) {
			setProjectPaths(fIndexCollection, fFileWrapper, set_contents);
		}
	}
	
	/**
	 * Creates the index for the project based on the paths registered
	 * in the project data
	 * 
	 * @return
	 */
	private SVDBIndexCollectionMgr createProjectIndex() {
		SVDBIndexCollectionMgr ret = new SVDBIndexCollectionMgr(fProjectName);
		SVProjectFileWrapper fw = getProjectFileWrapper();
		
		setProjectPaths(ret, fw, false);

		return ret;
	}
	
	private void setProjectPaths(
			SVDBIndexCollectionMgr 		sc,
			SVProjectFileWrapper		fw,
			boolean						refresh) {
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		Map<String, String> define_map = new HashMap<String, String>();
		Map<String, Object> args = new HashMap<String, Object>();
		
		for (Tuple<String, String> def : fw.getGlobalDefines()) {
			if (define_map.containsKey(def.first())) {
				define_map.remove(def.first());
			}
			define_map.put(def.first(), def.second());
		}
		
		sc.clear();

		// Add enabled plugin paths
		for (SVDBPath path : fw.getPluginPaths()) {
			ISVDBIndex index = rgy.findCreateIndex(
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
		
		args.clear();
		args.put(ISVDBIndexFactory.KEY_GlobalDefineMap, define_map);
		for (SVDBPath path : fw.getLibraryPaths()) {
			ISVDBIndex index = rgy.findCreateIndex(
					fProjectName, path.getPath(), 
					SVDBLibPathIndexFactory.TYPE, args);
			
			if (index != null) {
				sc.addLibraryPath(index);
			} else {
				fLog.error(
						"failed to create library index \"" +
						path.getPath() + "\"");
			}
		}
		
		args.clear();
		args.put(ISVDBIndexFactory.KEY_GlobalDefineMap, define_map);
		for (SVDBPath path : fw.getArgFilePaths()) {
			ISVDBIndex index = rgy.findCreateIndex(
					fProjectName, path.getPath(),
					SVDBArgFileIndexFactory.TYPE, args);
			
			if (index != null) {
				sc.addLibraryPath(index);
			} else {
				fLog.error(
						"failed to create arg-file index \"" +
						path.getPath() + "\"");
			}
		}
		
		for (SVDBSourceCollection srcc : fw.getSourceCollections()) {
			Map<String, Object> params = new HashMap<String, Object>();

			/*
			FileSet fs = new FileSet();
			params.put(SVDBSourceCollectionIndexFactory.FILESET, fs);
			 */
			ISVDBIndex index = rgy.findCreateIndex(
					fProjectName, srcc.getBaseLocation(),
					SVDBSourceCollectionIndexFactory.TYPE, params);
			
			if (index != null) {
				sc.addSourceCollection(index);
			} else {
				fLog.error(
						"failed to create source-collection index " +
						"\"" + srcc.getBaseLocation() + "\"");
			}
		}
		
		// Push defines to all indexes. This may cause index rebuild
		for (ISVDBIndex index : rgy.getProjectIndexList(fProjectName)) {
			for (Tuple<String, String> def : fw.getGlobalDefines()) {
				index.setGlobalDefine(def.first(), def.second());
			}
		}
		
		// Project settings have changed, so notify listeners
		for (ISVDBProjectSettingsListener l : fListeners) {
			l.projectSettingsChanged(this);
		}
		
		// Also notify global listeners
		if (refresh) {
			SVCorePlugin.getDefault().getProjMgr().projectSettingsChanged(this);
		}
	}
}

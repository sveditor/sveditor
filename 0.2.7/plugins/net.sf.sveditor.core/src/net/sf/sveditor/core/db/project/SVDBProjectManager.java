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
import java.util.List;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

public class SVDBProjectManager implements IResourceChangeListener {
	private WeakHashMap<IPath, SVDBProjectData>		fProjectMap;
	private List<ISVDBProjectSettingsListener>		fListeners;
	
	public SVDBProjectManager() {
		fProjectMap = new WeakHashMap<IPath, SVDBProjectData>();
		fListeners = new ArrayList<ISVDBProjectSettingsListener>();
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
	}
	
	public void init() {
		fProjectMap.clear();
	}
	
	public void addProjectSettingsListener(ISVDBProjectSettingsListener l) {
		fListeners.add(l);
	}
	
	public void removeProjectSettingsListener(ISVDBProjectSettingsListener l) {
		fListeners.remove(l);
	}
	
	void projectSettingsChanged(SVDBProjectData data) {
		for (ISVDBProjectSettingsListener l : fListeners) {
			l.projectSettingsChanged(data);
		}
	}
	
	public List<SVDBProjectData> getProjectList() {
		List<SVDBProjectData> ret = new ArrayList<SVDBProjectData>();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		for (IProject p : root.getProjects()) {
			if (p.isOpen() && p.getFile(".svproject").exists()) {
				SVDBProjectData pd = getProjectData(p);
				if (pd != null) {
					ret.add(pd);
				}
			}
		}
		
		return ret;
	}
	
	public SVDBProjectData getProjectData(IProject proj) {
		SVDBProjectData ret = null;
		
		if (fProjectMap.containsKey(proj.getFullPath())) {
			ret = fProjectMap.get(proj.getFullPath());
		} else {
			IFile svproject;
			SVProjectFileWrapper f_wrapper = null;
			if ((svproject = proj.getFile(".svproject")).exists()) {
				InputStream in = null;
				try {
					svproject.refreshLocal(IResource.DEPTH_ZERO, null);
					in = svproject.getContents();
				} catch (CoreException e) {
					e.printStackTrace();
				}

				try {
					f_wrapper = new SVProjectFileWrapper(in);
				} catch (Exception e) {
					// File format is bad
					f_wrapper = null;
				}
			}
			
			if (f_wrapper == null) {
				f_wrapper = new SVProjectFileWrapper();
				
				setupDefaultProjectFile(f_wrapper);
				
				// Write the file
				ByteArrayOutputStream bos = new ByteArrayOutputStream();
				f_wrapper.toStream(bos);
				ByteArrayInputStream bis = new ByteArrayInputStream(bos.toByteArray());
				
				try {
					if (svproject.exists()) {
						svproject.setContents(bis, true, true, null);
					} else {
						svproject.create(bis, true, null);
					}
				} catch (CoreException e) {
					e.printStackTrace();
				}
			}
			
			ret = new SVDBProjectData(proj.getName(), f_wrapper, svproject.getFullPath());
			
			fProjectMap.put(proj.getFullPath(), ret);
		}
		
		return ret;
	}

	/**
	 * Setup the default project data.
	 * - Includes default plugin libraries
	 * 
	 * @param file_wrapper
	 */
	private static void setupDefaultProjectFile(SVProjectFileWrapper file_wrapper) {
		List<SVDBPluginLibDescriptor> lib_d = SVCorePlugin.getDefault().getPluginLibList();
		
		for (SVDBPluginLibDescriptor d : lib_d) {
			if (d.isDefault()) {
				file_wrapper.getPluginPaths().add(new SVDBPath(d.getId()));
			}
		}
	}
	
	public void resourceChanged(IResourceChangeEvent event) {
		final List<IProject> changed_projects = new ArrayList<IProject>();
		
		if (event.getDelta() != null) {
			try {
				event.getDelta().accept(new IResourceDeltaVisitor() {
					
					public boolean visit(IResourceDelta delta)
							throws CoreException {
						IProject p = delta.getResource().getProject();
						if (p != null && 
								fProjectMap.containsKey(p.getFullPath()) &&
								!changed_projects.contains(p)) {
							changed_projects.add(p);
						}
						return true;
					}
				});
			} catch (CoreException e) {
			}
		}
		
		/*
		for (IProject p : changed_projects) {
			SVDBProjectData pd = fProjectMap.get(p.getFullPath());
			
			// re-scan project data file
			pd.refreshProjectFile();
		}
		 */
		
		// TODO: Now, iterate through the projects and re-scan the files
	}
	
	public void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}
}

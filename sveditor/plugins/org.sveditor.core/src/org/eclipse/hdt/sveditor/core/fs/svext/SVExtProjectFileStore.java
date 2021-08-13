/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.fs.svext;

import java.io.File;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.filesystem.IFileInfo;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileStore;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.sveditor.core.ISVProjectBuilderListener;
import org.sveditor.core.SVFileUtils;
import org.sveditor.core.db.index.ISVDBDeclCache;
import org.sveditor.core.db.project.SVDBProjectData;
import org.sveditor.core.log.ILogHandle;
import org.sveditor.core.log.ILogLevelListener;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

public class SVExtProjectFileStore extends FileStore implements ISVProjectBuilderListener {
	private SVDBProjectData				fProjData;
	private boolean						fRebuildScheduled;
	private SVExtFileStore				fRoot;
	private static boolean				fDebugEn;
	private static LogHandle			fLog;
	
	static {
		fLog = LogFactory.getLogHandle("SVExtProjectFileStore");
		fLog.addLogLevelListener(new ILogLevelListener() {
			
			@Override
			public void logLevelChanged(ILogHandle handle) {
				fDebugEn = handle.isEnabled();
			}
		});
		fDebugEn = fLog.isEnabled();
	}
	
	public SVExtProjectFileStore(SVDBProjectData pd) {
		fProjData = pd;
		
		fRoot = new SVExtFileStore(fProjData.getName());
		
		fProjData.addBuildListener(this);
		
		synchronized (fRebuildTreeJob) {
			fRebuildScheduled = true;
			fRebuildTreeJob.schedule();
		}
		
	}

	// Ignore
	@Override
	public void build_start(int kind, Map<String, String> args) { }


	@Override
	public void build_complete(int kind, Map<String, String> args) {
		synchronized (fRebuildTreeJob) {
			if (!fRebuildScheduled) {
				fRebuildTreeJob.schedule(100);
			}
		}
	}
	
	

	@Override
	public IFileStore getFileStore(IPath path) {
		// TODO Auto-generated method stub
		return super.getFileStore(path);
	}

	@Override
	public String[] childNames(int options, IProgressMonitor monitor) throws CoreException {
		Set<String> names = fRoot.getChildren().keySet();
		return names.toArray(new String[names.size()]);
	}

	@Override
	public IFileInfo fetchInfo(int options, IProgressMonitor monitor) throws CoreException {
		return fRoot.fetchInfo();
	}

	@Override
	public IFileStore getChild(String name) {
		return fRoot.getChild(name);
	}

	@Override
	public String getName() {
		return fRoot.getName();
	}

	@Override
	public IFileStore getParent() {
		return null;
	}

	@Override
	public InputStream openInputStream(int options, IProgressMonitor monitor) throws CoreException {
		return null;
	}
	
	@Override
	public URI toURI() {
		URI uri = null;
		try {
			uri = new URI("svext://" + fProjData.getName());
		} catch (URISyntaxException e) { }
		
		return uri;
	}
	
//	@Override
//	public File toLocalFile(int options, IProgressMonitor monitor) throws CoreException {
//		// TODO Auto-generated method stub
////		File ret = super.toLocalFile(options, monitor);
//		System.out.println("ProjectFileStore toLocalFile: options=" + options + " " + fProjData.getName());
//		return null;
////		return ret;
//	}

	
	private Job				fRebuildTreeJob = new Job("Rebuild External Files Tree") {
		
		@Override
		protected IStatus run(IProgressMonitor monitor) {
			Iterable<String> paths = fProjData.getProjectIndexMgr().getFileList(
					new NullProgressMonitor(), ISVDBDeclCache.FILE_ATTR_ARG_FILE);
			List<String> ext_paths = new ArrayList<String>();
	
			if (fDebugEn) {
				fLog.debug("RebuildTreeJob");
			}
			for (String path : paths) {
				if (!path.startsWith("${workspace_loc}") &&
						!path.startsWith("plugin:/")) {
					if (!ext_paths.contains(path)) {
						ext_paths.add(path);
					}
				}
			}
			paths = fProjData.getProjectIndexMgr().getFileList(
					new NullProgressMonitor(), ISVDBDeclCache.FILE_ATTR_SRC_FILE);
			for (String path : paths) {
				if (!path.startsWith("${workspace_loc}") &&
						!path.startsWith("plugin:/")) {
					if (!ext_paths.contains(path)) {
						ext_paths.add(path);
					}
				}
			}
			
			SVExtFileStore root = new SVExtFileStore(fProjData.getName());
			
			for (String ext_path : ext_paths) {
				List<String> path_elems = SVFileUtils.splitPath(ext_path);
				build_subtree(
						root, 
						null,
						fProjData.getName(), 
						path_elems, 
						0);
			}
			
			fRoot = root;
			
			IWorkspaceRoot ws = ResourcesPlugin.getWorkspace().getRoot();
			IProject p = ws.getProject(fProjData.getName());
		
			IFolder f = p.getFolder(SVExtFileSystem.EXT_SRC_DIRNAME);
			try {
				if (f.exists()) {
					f.refreshLocal(IResource.DEPTH_INFINITE, monitor);
				}
			} catch (CoreException e) { }			
			
			synchronized (fRebuildTreeJob) {
				fRebuildScheduled = false;
			}

			return Status.OK_STATUS;
		}
	};

	private void build_subtree(
			SVExtFileStore 		parent,
			File				file_prefix,
			String				path_prefix,
			List<String>		path,
			int					idx) {
		String name = path.get(idx);
		
		if (SVFileUtils.isWin() &&
				name.endsWith(":")) {
			name = name.substring(0, name.length()-1);
		}
		
		if (name.endsWith(":")) {
			fLog.error("failed to trim trailing colon");
		}
		
		File this_path;
		
		// Root
		if (file_prefix == null) {
			if (SVFileUtils.isWin()) {
				this_path = new File(path.get(idx) + "/");
			} else {
				this_path = new File("/" + path.get(idx));
			}
		} else {
			this_path = new File(file_prefix, path.get(idx));
		}
		
		if (!parent.getChildren().containsKey(name)) {

			
			SVExtFileStore elem = new SVExtFileStore(
					parent, path_prefix, name, this_path,
					(idx+1<path.size()));
			parent.getChildren().put(name, elem);
		}
		if (idx+1 < path.size()) {
			build_subtree(
					parent.getChildren().get(name),
					this_path,
					path_prefix + "/" + name,
					path, idx+1);
		}
	}
}

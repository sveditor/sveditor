package net.sf.sveditor.core.fs.svext;

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
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import net.sf.sveditor.core.ISVProjectBuilderListener;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public class SVExtProjectFileStore extends FileStore implements ISVProjectBuilderListener {
	private SVDBProjectData				fProjData;
	private boolean						fRebuildScheduled;
	private SVExtFileStore				fRoot;
	
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
		System.out.println("Project.getParent");
		return null;
	}

	@Override
	public InputStream openInputStream(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("Project.openInputStream");
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public URI toURI() {
		System.out.println("toURI");
		URI uri = null;
		try {
			uri = new URI("svext://" + fProjData.getName());
		} catch (URISyntaxException e) { }
		
		return uri;
	}
	
	private Job				fRebuildTreeJob = new Job("Rebuild External Files Tree") {
		
		@Override
		protected IStatus run(IProgressMonitor monitor) {
			Iterable<String> paths = fProjData.getProjectIndexMgr().getFileList(
					new NullProgressMonitor(), ISVDBDeclCache.FILE_ATTR_ARG_FILE);
			List<String> ext_paths = new ArrayList<String>();
		
			System.out.println("RebuildTreeJob");
			for (String path : paths) {
				System.out.println("Path: " + path);
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
				System.out.println("Path: " + path);
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
		
//			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
//			IProject p = root.getProject(fProjData.getName());
//		
//			fVirtualFolder = p.getFolder(SVExtFileSystem.EXT_SRC_DIRNAME);
//			try {
//				fVirtualFolder.refreshLocal(IResource.DEPTH_INFINITE, monitor);
//			} catch (CoreException e) { }
			
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
			System.out.println("Error: failed to trim training colon");
		}
		
		File this_path;
		
		// Root
		if (path_prefix == null) {
			if (SVFileUtils.isWin()) {
				this_path = new File(path.get(idx) + "/");
			} else {
				this_path = new File("/" + path.get(idx));
			}
		} else {
			this_path = new File(file_prefix, path.get(idx));
		}
		
		System.out.println("build_subtree: " + name);
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

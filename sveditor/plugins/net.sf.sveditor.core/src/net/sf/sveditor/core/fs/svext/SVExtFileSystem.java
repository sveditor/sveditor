package net.sf.sveditor.core.fs.svext;

import java.net.URI;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.IFileTree;
import org.eclipse.core.filesystem.provider.FileSystem;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public class SVExtFileSystem extends FileSystem {
//	private WeakHashMap<SVDBProjectData, SVExtProjectFileStore>	fProjectMap;
	private Map<SVDBProjectData, SVExtProjectFileStore>	fProjectMap;

	public SVExtFileSystem() { 
		fProjectMap = new HashMap<SVDBProjectData, SVExtProjectFileStore>();
	}

	@Override
	public IFileStore getStore(URI uri) {
		System.out.println("getStore: " + uri + " " + uri.getHost());
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IProject p = root.getProject(uri.getHost());
		if (p != null) {
			SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(p);
			if (!fProjectMap.containsKey(pd)) {
				fProjectMap.put(pd, new SVExtProjectFileStore(pd));
			}

			return fProjectMap.get(pd);
		} else {
			System.out.println("Error: failed to get project for " + uri.getPath());
		}
		return null;
	}

	@Override
	public IFileStore getStore(IPath path) {
		System.out.println("FileSystem.getStore: " + path);
		// TODO Auto-generated method stub
		return super.getStore(path);
	}

	@Override
	public IFileTree fetchFileTree(IFileStore root, IProgressMonitor monitor) throws CoreException {
		System.out.println("FileSystem.fetchFileTree: " + root);
		// TODO Auto-generated method stub
		return super.fetchFileTree(root, monitor);
	}

	
}

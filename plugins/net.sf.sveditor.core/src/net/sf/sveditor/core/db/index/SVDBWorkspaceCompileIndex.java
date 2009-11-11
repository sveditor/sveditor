package net.sf.sveditor.core.db.index;

import java.io.InputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

public class SVDBWorkspaceCompileIndex extends AbstractSVDBCompileIndex {
	
	public SVDBWorkspaceCompileIndex(String project_name) {
		super(project_name);
	}

	@Override
	protected long getLastModifiedTime(String path) {
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
		}
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		IFile file = root.getFile(new Path(path));
		
		return file.getModificationStamp();
	}

	@Override
	protected InputStream openStream(String path) {
		InputStream ret = null;
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
		}
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		IFile file = root.getFile(new Path(path));
		
		try {
			ret = file.getContents();
		} catch (CoreException e) { }
		
		
		return ret;
	}

}

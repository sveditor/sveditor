package net.sf.sveditor.core.db.index;

import java.io.InputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

public class SVDBWorkspaceArgFileIndex extends AbstractSVDBArgFileIndex {
	
	public SVDBWorkspaceArgFileIndex(
			String 			project_name,
			String			arg_file) {
		super(project_name, arg_file);
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

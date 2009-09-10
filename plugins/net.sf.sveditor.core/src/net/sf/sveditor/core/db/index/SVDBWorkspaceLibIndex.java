package net.sf.sveditor.core.db.index;

import java.io.InputStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.fileset.SVWorkspaceFileMatcher;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

public class SVDBWorkspaceLibIndex extends AbstractSVDBLibIndex {
	private String					fBaseLocation;
	private IFile					fLibFile;
	private IContainer				fLibDir;
	
	public SVDBWorkspaceLibIndex(
			String			project_name,
			String			base_location) {
		super(project_name, base_location);
		
		fBaseLocation = base_location;
		
		String full_path = fBaseLocation.substring("${workspace_loc}".length());
		
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();
		
		try {
			full_path = mgr.performStringSubstitution(full_path); 
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		fLibFile = root.getFile(new Path(full_path));
		
		if (fLibFile != null) {
			try {
				fLibDir = fLibFile.getParent();
				fLibFile.getParent().refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) { }
		}
		
		SVWorkspaceFileMatcher matcher = new SVWorkspaceFileMatcher();
		matcher.addFileSet(SVCorePlugin.getDefault().getDefaultFileSet(fLibFile.getParent().getFullPath().toOSString()));
		fFileMatchers.add(matcher);
		
		System.out.println("LibFile: " + fLibFile);
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
	
	@Override
	protected long getLastModifiedTime(String path) {
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
		}
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		IFile file = root.getFile(new Path(path));
		
		return file.getModificationStamp();
	}

	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public SVDBFile findIncludedFile(String leaf) {
		
		IFile target = fLibDir.getFile(new Path(leaf));
		String path = "${workspace_loc}" + target.getFullPath().toOSString();
		
		System.out.println("findIncludedFile: path=" + path);
		
		if (fFileIndex.containsKey(path)) {
			return fFileIndex.get(path);
		} else if (target.exists()) {
			SVDBFile pp_file = processPreProcFile(path);
			fFileIndex.put(path, pp_file);
			return pp_file;
		} else {
			return null;
		}
	}
	
	public String getTypeID() {
		return SVDBLibPathIndexFactory.TYPE;
	}

}

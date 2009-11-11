package net.sf.sveditor.core.fileset;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

public class SVWorkspaceFileMatcher extends AbstractSVFileMatcher {
	
	public SVWorkspaceFileMatcher() {
	}

	@Override
	public List<String> findIncludedPaths() {
		final List<String> ret = new ArrayList<String>();
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		for (SVFileSet fs : fFileSets) {
			String base_location = fs.getBase();
			
			if (base_location.startsWith("${workspace_loc}")) {
				base_location = base_location.substring("${workspace_loc}".length());
			}
			
			try {
				IResource base = root.findMember(base_location);
				
				if (base == null) {
					System.out.println("base \"" + base_location + "\" is null");
				}
				
				base.refreshLocal(IResource.DEPTH_INFINITE, null);
				final String base_loc = base.getFullPath().toOSString();
				base.accept(new IResourceVisitor(){

					public boolean visit(IResource resource) throws CoreException {
						if (resource instanceof IFile) {
							String full_path = ((IFile)resource).getFullPath().toOSString();
							String leaf = full_path.substring(base_loc.length());

							if (include_file(leaf)) {
								ret.add("${workspace_loc}" + full_path);
							}
						}
						return true;
					}
				});
			} catch (CoreException e) { }
		}
		
		return ret;
	}
}

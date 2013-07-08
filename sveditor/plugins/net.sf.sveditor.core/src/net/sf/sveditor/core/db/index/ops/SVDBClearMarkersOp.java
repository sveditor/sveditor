package net.sf.sveditor.core.db.index.ops;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.SVMarkers;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;

public class SVDBClearMarkersOp implements ISVDBIndexOperation {

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		monitor.beginTask("Clear markers for " + index.getBaseLocation(), 10000);
		Iterable<String> paths = index.getFileList(new NullProgressMonitor());
		
		final List<IProject> projects = new ArrayList<IProject>();
	
		// Build a list of projects
		for (String path : paths) {
			if (path.startsWith("${workspace_loc}")) {
				IFile file = SVFileUtils.getWorkspaceFile(path);
				
				if (file != null) {
					IProject p = file.getProject();
					if (!projects.contains(p)) {
						projects.add(p);
					}
				}
			}
		}
		
		for (IProject p : projects) {
			try {
				p.deleteMarkers(SVMarkers.TYPE_PROBLEM, true, IResource.DEPTH_INFINITE);
				p.deleteMarkers(SVMarkers.TYPE_TASK, true, IResource.DEPTH_INFINITE);
			} catch (CoreException e) {}
		}
		
		monitor.done();
	}

}

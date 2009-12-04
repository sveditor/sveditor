package net.sf.sveditor.core.db.index.src_collection;

import java.io.InputStream;

import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

public class SVDBWorkspaceSourceCollectionIndex extends SVDBSourceCollectionIndex 
		implements IResourceChangeListener, IResourceDeltaVisitor {

	public SVDBWorkspaceSourceCollectionIndex(
			String					project,
			String 					root,
			int						index_type,
			AbstractSVFileMatcher	matcher) {
		super(project, root, index_type, matcher, null);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
	}
	
	public void dispose() {
		super.dispose();
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}
	
	public String getTypeID() {
		return SVDBSourceCollectionIndexFactory.TYPE;
	}
	
	protected InputStream openStream(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		System.out.println("SVDBWorkspaceSource.openStream: " + path);
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
		}
		
		IFile file = root.getFile(new Path(path));
		
		InputStream in = null;
		
		int count = 0;
		while (true) {
			try {
				in = file.getContents();
			} catch (CoreException e) {
				if (e.getMessage().startsWith("Resource is out of sync") && count == 0) {
					count++;
					try {
						file.refreshLocal(IResource.DEPTH_ONE, null);
					} catch (CoreException e1) { }
					continue;
				}
				e.printStackTrace();
			}
			
			break;
		}
		
		return in;
	}
	
	protected long getLastModifiedTime(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
		}
		
		IFile file = root.getFile(new Path(path));
		
		return file.getModificationStamp();
	}

	public synchronized boolean visit(IResourceDelta delta) throws CoreException {
		
		if (delta.getResource() instanceof IFile) {
			String file = ((IFile)delta.getResource()).getFullPath().toOSString();
			
			if (delta.getKind() == IResourceDelta.REMOVED) {
				// remove from the queue (if present) and the index
				fileRemoved(file);
			} else if (delta.getKind() == IResourceDelta.ADDED) {
				fileAdded(file);
			} else {
				fileChanged(file);
			}
		}

		return true;
	}

	public void resourceChanged(IResourceChangeEvent event) {
		try {
			if (event.getDelta() != null) {
				event.getDelta().accept(this);
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
}

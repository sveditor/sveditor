package net.sf.sveditor.core;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

public class SVDBWorkspaceIndex extends SVDBIndexBase 
		implements IResourceChangeListener, IResourceDeltaVisitor {

	public SVDBWorkspaceIndex(
			IPath 				root,
			int					index_type) {
		super(root.toFile(), index_type);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
	}
	
	public void dispose() {
		super.dispose();
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}
	
	public synchronized boolean visit(IResourceDelta delta) throws CoreException {
		
		if (delta.getResource() instanceof IFile) {
			File file = ((IFile)delta.getResource()).getLocation().toFile();
			
			if (delta.getKind() == IResourceDelta.REMOVED) {
				// remove from the queue (if present) and the index
				System.out.println("[NOTE] file \"" + file.getAbsolutePath() + "\" removed");
			} else if (delta.getKind() == IResourceDelta.ADDED) {
				System.out.println("[NOTE] file \"" + file.getAbsolutePath() + "\" added");
			} else {
				System.out.println("[NOTE] file \"" + file.getAbsolutePath() + "\" changed");
			}
		}

		return true;
	}

	public void resourceChanged(IResourceChangeEvent event) {
		try {
			event.getDelta().accept(this);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
}

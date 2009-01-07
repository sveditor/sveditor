package net.sf.sveditor.core;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

public class SVDBWorkspaceIndex extends SVDBIndexBase 
		implements IResourceChangeListener, IResourceDeltaVisitor {

	public SVDBWorkspaceIndex(IPath root, ISVDBFileProvider provider) {
		super(root.toFile(), provider);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);

		IWorkspaceRoot ws = ResourcesPlugin.getWorkspace().getRoot();
		
		try {
			
			ws.findMember(root).accept(new IResourceVisitor() {

				public boolean visit(IResource resource) throws CoreException {
					if (resource instanceof IFolder &&
							fIgnoreDirs.contains(((IFolder)resource).getName())) {
						return false;
					}
					if (resource instanceof IFile) {
						String n = ((IFile)resource).getName();
						
						if (n.lastIndexOf('.') >= 0 && 
								fSVExtensions.contains(
										n.substring(n.lastIndexOf('.')))) {
							push(((IFile)resource).getLocation().toFile());
						}
					}
					return true;
				}
				
			});
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
	
	public void dispose() {
		super.dispose();
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}
	
	public boolean visit(IResourceDelta delta) throws CoreException {
		if (delta.getResource() instanceof IFile) {
			File file = ((IFile)delta.getResource()).getLocation().toFile();
			
			if (delta.getKind() == IResourceDelta.REMOVED) {
				// remove from the queue (if present) and the index
				
				synchronized (fFileQueue) {
					if (fFileQueue.contains(file)) {
						fFileQueue.remove(file);
					}
				}
				
				synchronized (fFileList) {
					for (int i=0; i<fFileList.size(); i++) {
						if (fFileList.get(i).getFilePath().equals(file)) {
							fFileList.remove(i);
							break;
						}
					}
				}
			} else {
				push(file);
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

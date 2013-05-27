package net.sf.sveditor.core;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent.Type;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

public class SVProjectBuilder extends IncrementalProjectBuilder {
	
	public static final String BUILDER_ID = "net.sf.sveditor.core.SVProjectBuilder";

	public SVProjectBuilder() {
		// TODO Auto-generated constructor stub
	}
	
	@Override
	protected IProject[] build(
			int 					kind, 
			Map<String, String> 	args,
			IProgressMonitor 		monitor) throws CoreException {
		IProject p = getProject();
		System.out.println("build kind: " + kind);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		switch (kind) {
			case CLEAN_BUILD:
			case FULL_BUILD:
				// Rebuild the target project
				pmgr.rebuildProject(monitor, p);
				break;
				
			case AUTO_BUILD:
			case INCREMENTAL_BUILD: {
				final List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
				IResourceDelta delta = getDelta(p);
				
				try {
					delta.accept(new IResourceDeltaVisitor() {
						
						public boolean visit(IResourceDelta delta) throws CoreException {
							SVDBIndexResourceChangeEvent.Type type = null;
							switch (delta.getKind()) {
								case IResourceDelta.CHANGED: 
									// We don't care about changes like markers
									if ((delta.getFlags() & IResourceDelta.CONTENT) != 0) {
										type = Type.CHANGE;
									}
									break;
								case IResourceDelta.REMOVED: 
									type = Type.REMOVE;
									break;
							}
							
							if (delta.getResource() instanceof IProject) {
								if ((delta.getFlags() & IResourceDelta.OPEN) != 0) {
									return false;
								} else if (delta.getKind() == IResourceDelta.REMOVED) {
									return false;
								}
							} else if (delta.getResource() instanceof IFile) {
								if (type != null) {
									changes.add(new SVDBIndexResourceChangeEvent(
											type, "${workspace_loc}" + delta.getResource().getFullPath()));
								}
							}
							
							return true;
						}
					});
					} catch (CoreException e) {}
				
					pmgr.rebuildProject(monitor, p, changes);
				} break;
		}

		// Don't need any delta right now...
		return null;
	}

}

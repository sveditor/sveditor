package net.sf.sveditor.core;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent.Type;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

public class SVResourceChangeListener implements IResourceChangeListener {
	private SVDBProjectManager				fProjectMgr;
	private boolean							fResourceListenerActive;
	
	
	public SVResourceChangeListener(SVDBProjectManager pmgr) {
		fProjectMgr = pmgr;
		init();
	}

	public synchronized void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
		fResourceListenerActive = false;
	}
	
	public synchronized void init() {
		if (!fResourceListenerActive) {
			ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
			fResourceListenerActive = true;
		}
	}

	public void resourceChanged(IResourceChangeEvent event) {
		final List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
		final SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
	
		debug("--> resourceChanged");
		String type = "UNKNOWN";
		switch (event.getType()) {
			case IResourceChangeEvent.PRE_CLOSE: type = "PRE_CLOSE"; break;
			case IResourceChangeEvent.PRE_BUILD: type = "PRE_BUILD"; break;
			case IResourceChangeEvent.PRE_DELETE: type = "PRE_DELETE"; break;
			case IResourceChangeEvent.PRE_REFRESH: type = "PRE_REFRESH"; break;
			case IResourceChangeEvent.POST_BUILD: type = "POST_BUILD"; break;
			case IResourceChangeEvent.POST_CHANGE: type = "POST_CHANGE"; break;
		}
		debug("resourceChanged: " + type + " " + event.getResource());
		
		if (event.getDelta() == null) {

			debug("Null delta: " + type + " " + event.getResource());
		} else if (event.getResource() instanceof IProject) {
			debug("Change to project");
		} else {
	
		try {
		event.getDelta().accept(new IResourceDeltaVisitor() {
			
			public boolean visit(IResourceDelta delta) throws CoreException {
				String kind = "UNKNOWN";
				SVDBIndexResourceChangeEvent.Type type = null;
				switch (delta.getKind()) {
					case IResourceDelta.ADDED: 
						type = Type.ADD;
						kind = "ADDED"; 
						break;
					case IResourceDelta.CHANGED: 
						// We don't care about changes like markers
						if ((delta.getFlags() & IResourceDelta.CONTENT) != 0) {
							type = Type.CHANGE;
						}
						kind = "CHANGED"; 
						break;
					case IResourceDelta.OPEN: kind = "OPEN"; break;
					case IResourceDelta.SYNC: kind = "SYNC"; break;
					case IResourceDelta.REMOVED: 
						type = Type.REMOVE;
						kind = "REMOVED"; 
						break;
				}
				
				if (delta.getResource() instanceof IProject) {
					IProject p = (IProject)delta.getResource();
//					System.out.println("Project Delta: " + delta.getKind() + " " + delta.getFlags());
					if ((delta.getFlags() & IResourceDelta.OPEN) != 0) {
						debug("delta: Project open/close -- " + delta.getFlags());
						if (p.isOpen()) {
							// Project opening or added
//							System.out.println("Project Opening");
							pmgr.projectOpened(p);
						} else {
							// Project closing
							pmgr.projectClosed(p);
						}
						return false;
					} else if (delta.getKind() == IResourceDelta.REMOVED) {
//						System.out.println("Project Removed");
						pmgr.projectRemoved(p);
						return false;
					}
				} else if (delta.getResource() instanceof IFile) {
					if (type != null) {
						debug("Delta " + kind + " " + 
								Integer.toHexString(delta.getFlags()) + " " +
								delta.getResource().getFullPath());
						/*
						changes.add(new SVDBIndexResourceChangeEvent(
								type, "${workspace_loc}" + delta.getResource().getFullPath()));
						 */
					}
				} else {
					debug("delta: " + kind + " " + delta.getResource() + " " + 
						Integer.toHexString(delta.getFlags()));
				}
				
				return true;
			}
		});
		} catch (CoreException e) {}
		}
		
		if (changes.size() > 0) {
			// 
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			rgy.notifyChanges(changes);
		}
		debug("<-- resourceChanged");
	}

	private void debug(String msg) {
//		System.out.println(msg);
	}
}

package net.sf.sveditor.core.builder;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent.Type;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVProjectBuilder extends IncrementalProjectBuilder implements ILogLevel {
	private LogHandle							fLog;
	
	public static final String BUILDER_ID = "net.sf.sveditor.core.SVProjectBuilder";

	public SVProjectBuilder() {
		// TODO Auto-generated constructor stub
		fLog = LogFactory.getLogHandle("SVProjectBuilder");
	}
	
	@Override
	protected IProject[] build(
			int 					kind, 
			Map<String, String> 	args,
			IProgressMonitor 		monitor) throws CoreException {
		IProject 			p = getProject();
		SVDBProjectManager 	pmgr = SVCorePlugin.getDefault().getProjMgr();
//		ISVBuilderOutput 	out = new SVBuilderOutput(p.getName(), 
//				SVCorePlugin.getDefault().getBuilderOutputListener());
	
		// Special test mode enabled
		if (SVCorePlugin.isTestModeBuilderDisabled()) {
			return null;
		}
		
		SVBuilderProcess process = new SVBuilderProcess(
				monitor, p, kind, args, getDelta(p));
	
		pmgr.startBuild(process, p, kind, args);
		
		process.run();

//		switch (kind) {
//		case IncrementalProjectBuilder.CLEAN_BUILD:
//		case IncrementalProjectBuilder.FULL_BUILD:
//			// Rebuild the target project
//			out.note("Running clean/full re-index of project " + p.getName());
//			pmgr.rebuildProject(monitor, p, out);
//			break;
//			
//		case IncrementalProjectBuilder.AUTO_BUILD:
//		case IncrementalProjectBuilder.INCREMENTAL_BUILD: {
//			out.note("Running incremental re-index of project " + p.getName());
//			
//			final List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
//			
//			try {
//				IResourceDelta delta = getDelta(p);
//				delta.accept(new IResourceDeltaVisitor() {
//					
//					public boolean visit(IResourceDelta delta) throws CoreException {
//						SVDBIndexResourceChangeEvent.Type type = null;
//						switch (delta.getKind()) {
//							case IResourceDelta.CHANGED: 
//								// We don't care about changes like markers
//								if ((delta.getFlags() & IResourceDelta.CONTENT) != 0) {
//									type = Type.CHANGE;
//								}
//								break;
//							case IResourceDelta.REMOVED: 
//								type = Type.REMOVE;
//								break;
//						}
//						
//						if (delta.getResource() instanceof IProject) {
//							if ((delta.getFlags() & IResourceDelta.OPEN) != 0) {
//								return false;
//							} else if (delta.getKind() == IResourceDelta.REMOVED) {
//								return false;
//							}
//						} else if (delta.getResource() instanceof IFile) {
//							if (type != null) {
//								changes.add(new SVDBIndexResourceChangeEvent(
//										type, "${workspace_loc}" + delta.getResource().getFullPath()));
//							}
//						}
//						
//						return true;
//					}
//				});
//				} catch (CoreException e) {}
//		
//				out.note("Total of " + changes.size() + " changes");
//				pmgr.rebuildProject(monitor, p, changes, out);
//			} break;
//		}
		
		pmgr.endBuild(p, kind, args);
		
		// Don't need any delta right now...
		return null;
	}

}

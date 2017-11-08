package net.sf.sveditor.core.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
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

		// Special test mode enabled
		if (SVCorePlugin.isTestModeBuilderDisabled()) {
			return null;
		}
		
		SVBuilderProcess process = new SVBuilderProcess(monitor, p);
	
		pmgr.startBuild(process, p, kind, args);
		
		process.build(kind, args, getDelta(p));

		pmgr.endBuild(p, kind, args);
		
		// Don't need any delta right now...
		return null;
	}

}

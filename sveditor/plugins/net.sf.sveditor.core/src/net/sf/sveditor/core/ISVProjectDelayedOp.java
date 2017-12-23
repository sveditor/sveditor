package net.sf.sveditor.core;

import org.eclipse.core.resources.IProject;

public interface ISVProjectDelayedOp {
	
	void projectBuildStarted(IProject p);
	
	boolean containsProject(IProject p);
	
}

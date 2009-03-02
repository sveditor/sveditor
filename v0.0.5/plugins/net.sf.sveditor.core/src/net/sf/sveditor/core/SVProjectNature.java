package net.sf.sveditor.core;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

public class SVProjectNature implements IProjectNature {
	private IProject				fProject;

	
	public void configure() throws CoreException {
		// TODO Auto-generated method stub

	}

	
	public void deconfigure() throws CoreException {
		// TODO Auto-generated method stub

	}

	
	public IProject getProject() {
		return fProject;
	}

	
	public void setProject(IProject project) {
		fProject = project;
	}

}

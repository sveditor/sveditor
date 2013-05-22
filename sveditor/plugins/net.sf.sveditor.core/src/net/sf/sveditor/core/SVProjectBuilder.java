package net.sf.sveditor.core;

import java.util.Map;

import org.eclipse.core.resources.IProject;
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
		
		// TODO Auto-generated method stub
//		System.out.println("build: " + kind);
	
		// Don't need any delta right now...
		return null;
	}

}

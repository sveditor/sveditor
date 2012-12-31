package net.sf.sveditor.core.argfile.parser;

import org.eclipse.core.resources.IProject;

public class SVArgFileProjectRsrcVarProvider extends
		SVArgFilePathVariableProvider {
	
	public SVArgFileProjectRsrcVarProvider(IProject project) {
		super(project.getPathVariableManager());
	}
	
}

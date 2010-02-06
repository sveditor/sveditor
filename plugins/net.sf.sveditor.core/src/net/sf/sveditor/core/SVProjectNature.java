/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


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

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

import net.sf.sveditor.core.db.project.SVDBProjectData;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdapterFactory;

public class SVProjectDataAdapter implements IAdapterFactory {

	@SuppressWarnings("rawtypes")
	public Object getAdapter(Object adaptableObject, Class adapterType) {
		if (adaptableObject instanceof IProject) {
			IProject p = (IProject)adaptableObject;
			
			if (p.getFile(".svproject").exists()) {
				SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(p);
				return pd;
			}
		}
		// TODO Auto-generated method stub
		return null;
	}

	@SuppressWarnings({ "rawtypes" })
	public Class[] getAdapterList() {
		return new Class[] {
				IProject.class
		};
	}


}

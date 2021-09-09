/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdapterFactory;
import org.sveditor.core.db.project.SVDBProjectData;

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

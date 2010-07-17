package net.sf.sveditor.core;

import net.sf.sveditor.core.db.project.SVDBProjectData;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdapterFactory;

public class SVProjectDataAdapter implements IAdapterFactory {

	@SuppressWarnings("unchecked")
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

	@SuppressWarnings("unchecked")
	public Class[] getAdapterList() {
		System.out.println("getAdapterList");
		return new Class[] {
				IProject.class
		};
	}


}

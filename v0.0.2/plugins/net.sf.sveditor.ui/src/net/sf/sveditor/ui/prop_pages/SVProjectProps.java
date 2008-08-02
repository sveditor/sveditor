package net.sf.sveditor.ui.prop_pages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * 
 * @author ballance
 *
 */
public class SVProjectProps extends PropertyPage implements
		IWorkbenchPropertyPage {

	public SVProjectProps() {
		// TODO Auto-generated constructor stub
	}

	@Override
	protected Control createContents(Composite parent) {
		Control ret = null;
		
		

		if (ret != null) {
			Dialog.applyDialogFont(ret);
		}
		return ret;
	}

	private IProject getProject() {
		IAdaptable adaptable = getElement();
		if (adaptable != null) {
			IProject proj = (IProject)adaptable.getAdapter(IProject.class);
			
			return proj;
		}
		return null;
	}

}

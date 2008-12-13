package net.sf.sveditor.ui.prop_pages;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectFileWrapper;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * 
 * @author ballance
 *
 */
public class SVProjectProps extends PropertyPage implements
		IWorkbenchPropertyPage {

	private SVDBProjectData				fProjectData;
	private SVProjectFileWrapper		fProjectFileWrapper;
	private SVProjectPathsPage			fBuildPathsPage;
	private SVProjectPathsPage			fIncludePathsPage;

	public SVProjectProps() {
		// TODO Auto-generated constructor stub
		
		noDefaultAndApplyButton();
	}

	@Override
	protected Control createContents(Composite parent) {

		IProject p = getProject();
		
		SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
		fProjectData = mgr.getProjectData(p);
		fProjectFileWrapper = fProjectData.getProjectFileWrapper().duplicate();
		
		TabFolder folder = new TabFolder(parent, SWT.NONE);
		
		TabItem item;
		
		item = new TabItem(folder, SWT.NONE);
		item.setText("Build Paths");
		fBuildPathsPage = new SVProjectPathsPage();
		fBuildPathsPage.init(fProjectFileWrapper.getBuildPaths());
		item.setControl(fBuildPathsPage.createContents(folder));
		
		item = new TabItem(folder, SWT.NONE);
		item.setText("Include Paths");
		fIncludePathsPage = new SVProjectPathsPage();
		fIncludePathsPage.init(fProjectFileWrapper.getIncludePaths());
		item.setControl(fIncludePathsPage.createContents(folder));
		

		Dialog.applyDialogFont(folder);
		
		return folder;
	}
	

	@Override
	public boolean performOk() {
		
		fProjectFileWrapper.getBuildPaths().clear();
		fProjectFileWrapper.getBuildPaths().addAll(
				fBuildPathsPage.getPathList());
		
		fProjectFileWrapper.getIncludePaths().clear();
		fProjectFileWrapper.getIncludePaths().addAll(
				fIncludePathsPage.getPathList());
		
		fProjectData.setProjectFileWrapper(fProjectFileWrapper);
		
		return true;
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

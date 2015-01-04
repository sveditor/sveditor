package net.sf.sveditor.ui.wizards.new_filelist;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.ui.SVEditorUtil;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PartInitException;

public class NewFileListWizard extends Wizard implements INewWizard {
	private IStructuredSelection					fSel;
	private NewFileListWizardFirstPage				fFirstPage;
	private NewFileListWizardAddFilesPage			fAddFilesPage;
	
	public NewFileListWizard() {
		setNeedsProgressMonitor(true);
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		fSel = selection;
	}
	
	public void addPages() {
		addPage((fFirstPage = new NewFileListWizardFirstPage()));
		addPage((fAddFilesPage = new NewFileListWizardAddFilesPage()));
		
		fFirstPage.init(fSel);
	}
	
	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		
		IWizardPage next = super.getNextPage(page);
		
		return next;
	}
	

	@Override
	public boolean canFinish() {
		if (getContainer().getCurrentPage() == fFirstPage && 
				fFirstPage.isPageComplete()) {
			return true;
		} else {
			return super.canFinish();
		}
	}

	@Override
	public boolean performFinish() {
		String dest = "${workspace_loc}" + 
				fFirstPage.getOutputDir().getFullPath() + "/" +
				fFirstPage.getFilename();
		OutputStream out = fAddFilesPage.getFSProvider().openStreamWrite(dest);
		PrintStream ps = new PrintStream(out);
		
		ps.println("/**");
		ps.println(" * Filelist: " + fFirstPage.getFilename());
		ps.println(" */");
		
		if (getContainer().getCurrentPage() == fAddFilesPage) {
			// Create content
			if (fAddFilesPage.updateRequired()) {
				fAddFilesPage.runUpdateOperation();
			}
			ps.println(fAddFilesPage.getArgFileContent());
		}

		ps.flush();
		fAddFilesPage.getFSProvider().closeStream(out);
		
		if (fFirstPage.getAddToProject()) {
			// Add file to the project
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			IProject p = fFirstPage.getOutputDir().getProject();

			String proj_rel_path = fFirstPage.getOutputDir().getFullPath().toString();
			proj_rel_path = proj_rel_path.substring(p.getName().length()+1);
			proj_rel_path = "${project_loc}" + proj_rel_path + "/" + fFirstPage.getFilename();
			
			SVDBProjectData pdata = pmgr.getProjectData(p);
			
			SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
			List<SVDBPath> argfile_paths = fw.getArgFilePaths();
			
			if (!argfile_paths.contains(dest) && !argfile_paths.contains(proj_rel_path)) {
				fw.addArgFilePath(proj_rel_path);
				
				pdata.setProjectFileWrapper(fw, true);
			}
		}
	
		try {
			SVEditorUtil.openEditor(dest);
		} catch (PartInitException e) {
		}
		
		return true;
	}

}

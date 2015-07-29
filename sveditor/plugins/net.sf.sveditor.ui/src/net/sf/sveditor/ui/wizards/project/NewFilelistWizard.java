package net.sf.sveditor.ui.wizards.project;

import java.io.File;
import java.util.Set;

import net.sf.sveditor.core.db.index.SVDBScopedFileSystemProvider;
import net.sf.sveditor.ui.content_providers.SVDBFileSystemContentProvider;
import net.sf.sveditor.ui.content_providers.SVDBFileSystemLabelProvider;
import net.sf.sveditor.ui.wizards.new_filelist.NewFileListWizardAddFilesPage;

import org.eclipse.jface.wizard.Wizard;

public class NewFilelistWizard extends Wizard {
	private NewFilelistWizardFirstPage			fNamePage;
	private NewFileListWizardAddFilesPage		fAddFilesPage;
	private File								fRoot;
	private String								fProjectName;
	private Set<String>							fExistingPaths;
	
	public NewFilelistWizard(
			File 			root, 
			String			pname,
			Set<String> 	existing_paths) {
		fRoot = root;
		fProjectName = pname;
		fExistingPaths = existing_paths;
	}
	
	@Override
	public void addPages() {
		fNamePage = new NewFilelistWizardFirstPage(fExistingPaths);
		addPage(fNamePage);

		SVDBScopedFileSystemProvider fs_provider = new SVDBScopedFileSystemProvider();
		fs_provider.init(fRoot.getAbsolutePath());
		
		fAddFilesPage = new NewFileListWizardAddFilesPage(
				new SVDBFileSystemContentProvider(),
				new SVDBFileSystemLabelProvider(fs_provider),
				fs_provider,
				fs_provider);
	
		// The path used by AddFilesPage is /<project_name>
		fAddFilesPage.setPrefix(".", fProjectName.length()+1);
		addPage(fAddFilesPage);
	}
	
	public String getArgFileContent() {
		return fAddFilesPage.getArgFileContent();
	}
	
	public String getPath() {
		return fNamePage.getPath();
	}


	@Override
	public boolean performFinish() {
		return true;
	}

}

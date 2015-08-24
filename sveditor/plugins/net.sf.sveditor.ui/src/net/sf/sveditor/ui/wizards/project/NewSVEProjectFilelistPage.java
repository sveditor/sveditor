package net.sf.sveditor.ui.wizards.project;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.ui.WorkspaceFileDialog;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;

public class NewSVEProjectFilelistPage extends WizardPage 
	implements SelectionListener, ISelectionChangedListener {
	
	public static class PathInfo {
		public String				fPath;
		public String				fNewContent;
		
		public PathInfo(String path) {
			fPath = path;
			fNewContent = null;
		}
		
		public PathInfo(String path, String content) {
			fPath = path;
			fNewContent = content;
		}
		
		public String toString() {
			return fPath;
		}
	}
	
	private WizardNewProjectCreationPage			fNamePage;
	private ListViewer								fPathListView;
	private List<PathInfo>							fPathList;
	private Button									fNewFilelistButton;
	private Button									fAddProjectPath;
	private Button									fAddWorkspacePath;
//	private Button									fAddFilesystemPath;
	private Button									fRemove;
	
	
	public NewSVEProjectFilelistPage(WizardNewProjectCreationPage name_page) {
		super("Specify Filelists");
		
		setTitle("Specify Filelists");

		fNamePage = name_page;
		fPathList = new ArrayList<NewSVEProjectFilelistPage.PathInfo>();
	}
	
	public List<PathInfo> getPathList() {
		return fPathList;
	}

	@Override
	public void createControl(Composite parent) {
		Composite top = new Composite(parent, SWT.NONE);
		top.setLayout(new GridLayout(2, false));
		
		fPathListView = new ListViewer(top);
		fPathListView.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Composite c = new Composite(top, SWT.NONE);
		c.setLayout(new GridLayout());
		c.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
		
		fPathListView.setContentProvider(fContentProvider);
		fPathListView.setLabelProvider(new LabelProvider());
		fPathListView.setInput(fPathList);
		fPathListView.addSelectionChangedListener(this);
		
		fNewFilelistButton = new Button(c, SWT.PUSH);
		fNewFilelistButton.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
		fNewFilelistButton.setText("New...");
		fNewFilelistButton.addSelectionListener(this);
		
		fAddProjectPath = new Button(c, SWT.PUSH);
		fAddProjectPath.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
		fAddProjectPath.setText("Add Project Path...");
		fAddProjectPath.addSelectionListener(this);
		
		fAddWorkspacePath = new Button(c, SWT.PUSH);
		fAddWorkspacePath.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
		fAddWorkspacePath.setText("Add Workspace Path...");
		fAddWorkspacePath.addSelectionListener(this);
		
//		fAddFilesystemPath = new Button(c, SWT.PUSH);
//		fAddFilesystemPath.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
//		fAddFilesystemPath.setText("Add Filesystem Path...");
//		fAddFilesystemPath.addSelectionListener(this);
		
		fRemove = new Button(c, SWT.PUSH);
		fRemove.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
		fRemove.setText("Remove");
		fRemove.addSelectionListener(this);
		fRemove.setEnabled(false);
		
		setControl(c);
	}

	@Override
	public void setVisible(boolean visible) {
		super.setVisible(visible);
		
		File parent_path = fNamePage.getLocationPath().toFile();
		File project_path = new File(parent_path, fNamePage.getProjectName());
		
		fAddProjectPath.setEnabled(project_path.isDirectory());
		fAddWorkspacePath.setEnabled(ResourcesPlugin.getWorkspace().getRoot().getProjects().length > 0);
	}

	private IStructuredContentProvider fContentProvider = new IStructuredContentProvider() {
		
		@Override
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }
		
		@Override
		public void dispose() { }
		
		@Override
		public Object[] getElements(Object inputElement) {
			return fPathList.toArray();
		}
	};
	
	private PathInfo newFileList() {
		PathInfo path = null;
		
		File parent_path = fNamePage.getLocationPath().toFile();
		final File project_path = (!fNamePage.useDefaults())?parent_path:
			new File(parent_path, fNamePage.getProjectName());
		
		if (project_path.isDirectory()) {
			// Launch more-involved new-filelist wizard
			final Set<String> existing_paths = new HashSet<String>();
			for (PathInfo pi : fPathList) {
				String p = pi.fPath;
				if (p.startsWith("${project_loc}/")) {
					p = p.substring("${project_loc}/".length());
				}
				existing_paths.add(p);
			}
			
			INewFilelistWizardPathValidator validator = new INewFilelistWizardPathValidator() {
				
				@Override
				public Tuple<String, String> isValid(String path) {
					Tuple<String, String> ret = new Tuple<String, String>(null, null);
					
					if (existing_paths.contains(path)) {
						ret.second("Duplicate filelist name \"" + path + "\"");
					} else {
						// See if the path already exists in the directory
						File file = new File(project_path, path);
						
						if (file.isFile()) {
							ret.first("Duplicate filelist name \"" + path + "\"");
						} else if (file.isDirectory()) {
							ret.second("Path is a directory");
						}
					}

					return ret;
				}
			};
			NewFilelistWizard wiz = new NewFilelistWizard(
					project_path, fNamePage.getProjectName(), validator);
			WizardDialog dlg = new WizardDialog(getShell(), wiz);
			dlg.setPageSize(530, 560);
			
			dlg.create();
			if (dlg.open() == Window.OK) {
				path = new PathInfo(
						"${project_loc}/" + wiz.getPath(), 
						wiz.getArgFileContent());
			}
		} else {
			InputDialog dlg = new InputDialog(getShell(), 
					"New Filelist",
					"Specify new filelist name",
					"sve.f",
					new IInputValidator() {
						
						@Override
						public String isValid(String path) {
							if (path.trim().length() == 0) {
								return "Must specify a path";
							}
							
							for (PathInfo p : fPathList) {
								if (p.fPath.equals("${project_loc}/" + path.trim())) {
									return "Duplicate filelist";
								}
							}
							
							return null;
						}
					});

			if (dlg.open() == Dialog.OK) {
				path = new PathInfo("${project_loc}/" + dlg.getValue().trim());
				path.fNewContent = 
						"//***************************************************************************\n" +
				        "//* " + dlg.getValue().trim() + "\n" +
						"//***************************************************************************\n" +
				        "\n" +
						" // List file paths and processing directives here\n" +
				        "\n"
						;
			}				
		}

		return path;
	}


	@Override
	public void widgetSelected(SelectionEvent e) {
		PathInfo path = null;
		
		if (e.widget == fNewFilelistButton) {
			path = newFileList();
		} else if (e.widget == fAddProjectPath) {
			File parent_path = fNamePage.getLocationPath().toFile();
			File project_path = new File(parent_path, fNamePage.getProjectName());
			
			ScopedFileSelectionDialog dlg = new ScopedFileSelectionDialog(getShell(), project_path);
			
			if (dlg.open() == Window.OK) {
				path = new PathInfo("${project_loc}" + dlg.getPath().replace('\\', '/'));
			}
		} else if (e.widget == fAddWorkspacePath) {
			WorkspaceFileDialog dlg = new WorkspaceFileDialog(getShell());
			
			if (dlg.open() == Window.OK) {
				path = new PathInfo("${workspace_loc}" + 
						dlg.getPath().replace('\\', '/'));
			}
		} else if (e.widget == fRemove) {
			IStructuredSelection sel = (IStructuredSelection)fPathListView.getSelection();
			for (Object sel_e : sel.toList()) {
				fPathList.remove(sel_e);
			}
			fPathListView.refresh();
		}
		
		if (path != null) {
			fPathList.add(path);
			fPathListView.refresh();
		}
	}

	@Override
	public void widgetDefaultSelected(SelectionEvent e) { }

	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		fRemove.setEnabled(!event.getSelection().isEmpty());
	}
	
}

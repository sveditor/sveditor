package net.sf.sveditor.ui.wizards.imp.compilation.args;


import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.argcollector.BaseArgCollector;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileToken;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.ui.WorkspaceDirectoryDialog;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;

public class CompilationArgImportSrcInfoPage extends WizardPage {
	private Text						fDestDirText;
	private String						fDestDir;
	private Button						fDestDirBrowse;
	
	private Text						fDestFileText;
	private String						fDestFile;
	
	private Text						fSrcDir;
	private Button						fSrcDirBrowse;
	private String						fSrcDirStr;
	
	private Text						fImportCmdText;
	private String						fImportCmd;
	
	private Button						fImportButton;
	private boolean						fImportRun;
	
	private Text						fImportCmdOutputText;
	
	private Text						fImportCmdArgsText;
	
	private String						fCapturedArgs;
	
	private SVDBWSFileSystemProvider	fFSProvider;
	
	public CompilationArgImportSrcInfoPage() {
		super("Source Info");
		fFSProvider = new SVDBWSFileSystemProvider();
		
		fSrcDirStr = "";
		fDestDir = "";
	}
	
	public void setDestDir(String dir) {
		fDestDir = (dir != null)?dir:"";
		if (fDestDirText != null) {
			fDestDirText.setText(fDestDir);
		}
	}
	
	public void setSrcDir(String dir) {
		fSrcDirStr = (dir != null)?dir:"";
		if (fSrcDir != null) {
			fSrcDir.setText(fSrcDirStr);
		}
	}
	
	public String getDestFile() {
		return fDestFile;
	}
	
	public String getDestDir() {
		return fDestDir;
	}
	
	public String getCapturedArgs() {
		return fCapturedArgs;
	}

	public void createControl(Composite parent) {
		GridData gd;
		SashForm sash = new SashForm(parent,  SWT.VERTICAL);
		sash.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Composite top = new Composite(sash, SWT.BORDER);
		top.setLayout(new GridLayout(3, false));

		Label l;
		Group g;
	
		/*
		g = new Group(top, SWT.BORDER);
		g.setText("Output")
		 */
		
		// Output information
		l = new Label(top, SWT.NONE);
		l.setText("Destination Directory:");
		fDestDirText = new Text(top, SWT.BORDER);
		fDestDirText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fDestDirBrowse = new Button(top, SWT.PUSH);
		fDestDirBrowse.setText("Browse...");
		fDestDirBrowse.addSelectionListener(selectionListener);
		
		l = new Label(top, SWT.NONE);
		l.setText("Destination File:");
		fDestFileText = new Text(top, SWT.BORDER);
		fDestFileText.addModifyListener(textModifyListener);
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fDestFileText.setLayoutData(gd);

		g = new Group(top, SWT.BORDER);
		g.setText("Compilation Command");
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout(3, false));
		
		// Import arguments
		l = new Label(g, SWT.NONE);
		l.setText("Command:");
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fImportCmdText = new Text(g, SWT.SINGLE+SWT.BORDER);
		fImportCmdText.setLayoutData(gd);
		fImportCmdText.addModifyListener(textModifyListener);
		
		// Source directory
		l = new Label(g, SWT.NONE);
		l.setText("Working Directory:");
		
		fSrcDir = new Text(g, SWT.SINGLE+SWT.BORDER);
		fSrcDir.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fSrcDir.addModifyListener(textModifyListener);
		
		fSrcDirBrowse = new Button(g, SWT.PUSH);
		fSrcDirBrowse.setText("Browse");
		fSrcDirBrowse.addSelectionListener(selectionListener);
	
		
		fImportButton = new Button(top, SWT.PUSH);
		fImportButton.setText("Run Compilation Command");
		gd = new GridData(SWT.CENTER, SWT.FILL, true, false);
		gd.horizontalSpan = 3;
		fImportButton.setLayoutData(gd);
		fImportButton.addSelectionListener(selectionListener);
		
		Composite bottom = new Composite(sash, SWT.BORDER);
		bottom.setLayout(new GridLayout());
		bottom.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		TabFolder output_args = new TabFolder(bottom, SWT.NONE);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		output_args.setLayoutData(gd);
		
		TabItem output = new TabItem(output_args, SWT.NONE);
		
		fImportCmdOutputText = new Text(output_args, 
				SWT.MULTI+SWT.V_SCROLL+SWT.H_SCROLL+SWT.READ_ONLY);
		output.setControl(fImportCmdOutputText);
		output.setText("Command Output");
		
		TabItem args = new TabItem(output_args, SWT.NONE);
		
		fImportCmdArgsText = new Text(output_args,
				SWT.MULTI+SWT.V_SCROLL+SWT.H_SCROLL+SWT.READ_ONLY);
		fImportCmdArgsText.addModifyListener(textModifyListener);
		args.setControl(fImportCmdArgsText);
		args.setText("Captured Arguments");
		
		fDestDirText.setText(fDestDir);
		fSrcDir.setText(fSrcDirStr);
		
		validate();
		
		setControl(sash);
	}
	
	private void runCompilation() {
		Job job = new Job("Run Import") {
			
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				BaseArgCollector collector = new BaseArgCollector();
				
				collector.addStderrListener(fLineListener);
				collector.addStdoutListener(fLineListener);
				
				// Build up an argument list
				List<String> args = new ArrayList<String>();
				SVArgFileLexer lexer = new SVArgFileLexer();
				SVArgFileToken tok;
				lexer.init(null, new StringTextScanner(fImportCmd));
				
				while ((tok = lexer.consumeToken()) != null) {
					if (tok.isOption()) {
						if (tok.getOptionOp() != null) {
							args.add(tok.getImage() + tok.getOptionOp() + tok.getOptionVal());
						} else {
							args.add(tok.getImage());
						}
					} else {
						args.add(tok.getImage());
					}
				}
				
				setCapturedArgs("");
			
				String srcdir = fSrcDirStr.trim();
				File srcdir_f = SVFileUtils.getLocation(srcdir);
				Exception exception = null;

				try {
					collector.process(srcdir_f, args);
				} catch (IOException e) {
					exception = e;
				}
			
				SVFileUtils.refresh(srcdir);
				
				if (exception == null) {
					fCapturedArgs = collector.getArguments();
				
					setCapturedArgs(collector.getArguments());
					fImportRun = true;
				} else {
					fCapturedArgs = "";
					setCapturedArgs(fCapturedArgs);
					setCommandError(exception.getMessage());
					fImportRun = false;
				}
				
				Display.getDefault().asyncExec(new Runnable() {
					public void run() {
						validate();
					}
				});
				
				return Status.OK_STATUS;
			}
		};
		job.setUser(true);
		job.schedule();

		/*
		try {
			job.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		 */
	}
	
	private ILineListener			fLineListener = new ILineListener() {
		public void line(final String l) {
			Display.getDefault().asyncExec(new Runnable() {
				public void run() {
					fImportCmdOutputText.append(l + "\n");
				}
			});
		}
	};
	
	private void setCapturedArgs(String args) {
		fCapturedArgs = args;
		
		if (fCapturedArgs == null) {
			fCapturedArgs = "";
		}
		Display.getDefault().asyncExec(new Runnable() {
			
			public void run() {
				fImportCmdArgsText.setText(fCapturedArgs);
			}
		});
	}
	
	private void setCommandError(final String out) {
		Display.getDefault().asyncExec(new Runnable() {
			
			public void run() {
				fImportCmdOutputText.setText(out);
			}
		});
	}
	
	private void validate() {
		setErrorMessage(null);
		boolean have_command = true;
		
		if (fDestDirText.getText().trim().equals("") ||
				!fFSProvider.isDir("${workspace_loc}" + fDestDirText.getText().trim())) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a destination directory");
			}
		}
		
		if (fDestFileText.getText().trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a destination file");
			}
		}

		// Check whether src path exists
		if (fSrcDir.getText().trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must Specify Source Directory");
			}
			have_command = false;
		}
		
		if (!fFSProvider.isDir(fSrcDir.getText().trim())) {
			if (getErrorMessage() == null) {
				setErrorMessage("Source Directory does not exist");
			}
			have_command = false;
		}
		
		if (fImportCmdText.getText().trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a command to run");
			}
			have_command = false;
		}
		
		
		fImportButton.setEnabled(have_command);

		if (!have_command) {
			fImportRun = false;
		}
		
		if (fImportCmdArgsText.getText().trim().equals("")) {
			if (have_command && fImportRun) {
				if (getErrorMessage() == null) {
					setErrorMessage("No compiler arguments found");
				}
			} else {
				if (getErrorMessage() == null) {
					setErrorMessage("Must run compilation");
//					setErrorMessage("Must run command");
				}
			}
		}
		
		if (!fImportRun) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must run compilation");
			}
		}
		
		setPageComplete((getErrorMessage() == null));
	}

	private ModifyListener				textModifyListener = new ModifyListener() {
		public void modifyText(ModifyEvent e) {
			Object src = e.getSource();
			
			if (src == fDestDirText) {
				fDestDir = fDestDirText.getText();
			}
			
			if (src == fDestFileText) {
				fDestFile = fDestFileText.getText();
			}
			
			if (src == fSrcDir) {
				fSrcDirStr = fSrcDir.getText();
			}

			if (src == fImportCmdText) {
				fImportCmd = fImportCmdText.getText();
			}
			
			if (src == fImportCmdText ||
					src == fDestFileText || src == fSrcDir) {
				if (fImportCmdOutputText != null) {
					fImportCmdOutputText.setText("");
				}
				if (fImportCmdArgsText != null) {
					fImportCmdArgsText.setText("");
				}
				fImportRun = false;
			}
			
			validate();
		}
	};
	
	private SelectionListener				selectionListener = new SelectionListener() {
		
		public void widgetSelected(SelectionEvent e) {
			Object src = e.getSource();
			
			if (src == fDestDirBrowse) {
				WorkspaceDirectoryDialog dlg = new WorkspaceDirectoryDialog(fDestDirBrowse.getShell());
				dlg.setInitialPath(fDestDirText.getText().trim());
				
				if (dlg.open() == Window.OK) {
					fDestDirText.setText(dlg.getPath());
				}
			} else if (src == fSrcDirBrowse) {
				BrowseDirectoryPathDialog dlg = new BrowseDirectoryPathDialog(fSrcDir.getShell());
				dlg.setInitialPath(fSrcDir.getText());
				
				if (dlg.open() == Window.OK) {
					fSrcDir.setText(dlg.getPath());
				}
			} else if (src == fImportButton) {
				runCompilation();
			}
		}
		
		public void widgetDefaultSelected(SelectionEvent e) { }
	};

}

package net.sf.sveditor.ui.wizards.imp.compilation.args;


import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.argcollector.ArgCollectorFactory;
import net.sf.sveditor.core.argcollector.IArgCollector;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class CompilationArgImportSrcInfoPage extends WizardPage {
	private Text					fSrcDir;
	private Button					fSrcDirBrowse;
	private String					fSrcDirStr;
	
	private Text					fImportCmdText;
	private String					fImportCmd;
	
	private Button					fImportButton;
	
	private Text					fImportCmdOutputText;
	private StringBuilder			fImportCmdOutput;
	
	public CompilationArgImportSrcInfoPage() {
		super("Source Info");
		fImportCmdOutput = new StringBuilder();
	}

	public void createControl(Composite parent) {
		GridData gd;
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));

		Label l;
		
		// Source directory
		l = new Label(c, SWT.NONE);
		l.setText("Source Directory:");
		
		fSrcDir = new Text(c, SWT.SINGLE+SWT.BORDER);
		fSrcDir.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		
		fSrcDirBrowse = new Button(c, SWT.PUSH);
		fSrcDirBrowse.setText("Browse");
	
		// Import arguments
		Group g;
	
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		
		g = new Group(c, SWT.BORDER);
		g.setText("Import Command");
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		
		fImportCmdText = new Text(g, SWT.MULTI);
		fImportCmdText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fImportButton = new Button(c, SWT.PUSH);
		fImportButton.setText("Run Compilation Command");
		gd = new GridData(SWT.CENTER, SWT.FILL, false, false);
		gd.horizontalSpan = 3;
		fImportButton.setLayoutData(gd);
		fImportButton.addSelectionListener(new SelectionListener() {
			
			public void widgetSelected(SelectionEvent e) {
				runCompilation();
			}
			
			public void widgetDefaultSelected(SelectionEvent e) { }
		});
	
		g = new Group(c, SWT.BORDER);
		g.setText("Import Command Output");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fImportCmdOutputText = new Text(g, 
				SWT.MULTI+SWT.V_SCROLL+SWT.H_SCROLL);
		fImportCmdOutputText.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		
		setControl(c);
	}
	
	private void runCompilation() {
		Job job = new Job("Run Import") {
			
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				IArgCollector collector = ArgCollectorFactory.create();
				
				collector.addStderrListener(fLineListener);
				collector.addStdoutListener(fLineListener);
			
				List<String> args = new ArrayList<String>();
				args.add("./runtest");
				args.add("build");
				try {
					System.out.println("--> Process");
				collector.process(
						new File("/home/ballance/p4views/vtech/collateral/ae_training/cov_closure_2013/uvm_ethmac/sim"),
						args);
					System.out.println("<-- Process");
				} catch (IOException e) {
					e.printStackTrace();
				}
				
				System.out.println("Arguments: " + collector.getArguments());
				
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
			System.out.println("Line: " + l);
			Display.getDefault().asyncExec(new Runnable() {
				public void run() {
					System.out.println("AppendLine: " + l);
					fImportCmdOutputText.append(l + "\n");
				}
			});
		}
	};

}

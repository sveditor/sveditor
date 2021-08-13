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
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package org.sveditor.ui.wizards ;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.sveditor.core.docs.DocGenConfig;
import org.sveditor.core.docs.IDocWriter;
import org.sveditor.core.docs.html.HTMLDocWriter;
import org.sveditor.core.docs.model.DocModel;
import org.sveditor.core.docs.model.DocModelFactory;
import org.sveditor.core.log.ILogLevel;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.browser.IWebBrowser;
import org.eclipse.ui.browser.IWorkbenchBrowserSupport;

public class DocGenWizard extends Wizard {
	
	DocGenSelectPkgsWizardPage fSelectPkgsPage ;
	DocGenBasicOptionsWizardPage fBasicOptionsPage ;
	
	IWorkbench workbench ;
	
	LogHandle log ;
	
	public DocGenWizard() {
		log = LogFactory.getLogHandle("DocGenWizard") ;
	}

	@Override
	public boolean performFinish() {
		final DocGenConfig cfg = new DocGenConfig() ;

		cfg.setPkgSet(fSelectPkgsPage.getSelectedPackages());
	
		cfg.setOutputDir(new File(fBasicOptionsPage.getOutputDir())) ;
		
		cfg.fPackagesSelected = fSelectPkgsPage.fSelectPackages ;

		try {
			getContainer().run(true, true, new IRunnableWithProgress() {
				public void run(IProgressMonitor monitor) 
						throws InvocationTargetException, InterruptedException {
					performOperation(cfg, monitor) ;
				}
			}) ;
		} catch (InvocationTargetException e) {
			log.error("Wizzard invocation failed", e) ;
		} catch (InterruptedException e) { 
			log.debug(ILogLevel.LEVEL_MIN, "Wizzard interrupted", e) ;
		}
		return true ;
	}

	public void init(IWorkbench workbench) {
		this.workbench = workbench ;
	}

	@Override
	public void addPages() {
		super.addPages() ;
		setWindowTitle("Generate Documentation Set") ;
		fSelectPkgsPage = new DocGenSelectPkgsWizardPage() ;
		addPage(fSelectPkgsPage) ;
		fBasicOptionsPage = new DocGenBasicOptionsWizardPage() ;
		addPage(fBasicOptionsPage) ;
	}

	@Override
	public boolean canFinish() {
		return (fSelectPkgsPage.hasSelection() ||fSelectPkgsPage.fSelectPackages==false)
				&& !(fBasicOptionsPage.getOutputDir().isEmpty()) ;
	}

	@Override
	public boolean performCancel() {
		return super.performCancel() ;
	}

	private void performOperation(DocGenConfig cfg, IProgressMonitor monitor) {
		class DocGenJob extends Job {
			private final DocGenConfig cfg ;
			public DocGenJob(String jobTitle, DocGenConfig cfg) {
				super(jobTitle) ;
				this.cfg = cfg ;
			}
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				monitor.beginTask("Doc Generation", 2);
				DocModelFactory factory = new DocModelFactory() ;
				DocModel model = factory.build(cfg) ;
				monitor.worked(1) ;
				IDocWriter writer = new HTMLDocWriter() ;
				writer.write(cfg, model) ;
				monitor.worked(1) ;
				final File file = writer.getIndexHTML(cfg, model) ;
				/* Internal browsers require access to the display so
				 * we must sync back up with the UI thread */
				Display.getDefault().asyncExec(new Runnable() {
					public void run() { openIndexHTML(file) ; }
				}) ;
				monitor.done() ;
				return Status.OK_STATUS ;
			}
			private void openIndexHTML(File indexHTML) {
				try {
					URL url = new URL("file://" + indexHTML) ;
					IWorkbenchBrowserSupport browserSupport = workbench.getBrowserSupport() ;
					IWebBrowser browser ;
					int style = IWorkbenchBrowserSupport.AS_EDITOR ;
					browser = browserSupport
							.createBrowser(style, "SVEditor HTML Docs", "SVEditor HTML docs", "SVEditor HTML docs") ;
					browser.openURL(url) ;
				} catch (Exception e) {
					log.error("Failed to open browser", e) ; 
					return ;
				}
			}
		}
		DocGenJob job = new DocGenJob("Documentation Generation", cfg) ;
		job.schedule() ;
	}
	
	

}

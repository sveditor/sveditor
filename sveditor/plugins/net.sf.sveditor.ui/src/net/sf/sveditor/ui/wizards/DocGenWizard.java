/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.ui.wizards ;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.net.MalformedURLException;
import java.net.URL;

import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.IDocWriter;
import net.sf.sveditor.core.docs.html.HTMLDocWriter;
import net.sf.sveditor.core.docs.model.DocModelFactory;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PartInitException;
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
		cfg.setSelectedPackages(fSelectPkgsPage.getSelectedPackages()) ;
		cfg.setOutputDir(new File(fBasicOptionsPage.getOutputDir())) ;
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
		return fSelectPkgsPage.hasSelection() 
				&& !(fBasicOptionsPage.getOutputDir().isEmpty()) ;
	}

	@Override
	public boolean performCancel() {
		return super.performCancel() ;
	}

	private void performOperation(DocGenConfig cfg, IProgressMonitor monitor) {
		monitor.beginTask("Generating documentation", 3) ;
		
		DocModelFactory factory = new DocModelFactory() ;
		DocModel model = factory.build(cfg) ;
		
		monitor.worked(1) ;
		IDocWriter writer = new HTMLDocWriter() ;
		writer.write(cfg, model) ;
		monitor.worked(1) ;
		openIndexHTML(writer.getIndexHTML(cfg, model)) ;
		monitor.done() ;
	}
	
	private void openIndexHTML(File indexHTML) {
		IWorkbenchBrowserSupport browserSupport = workbench.getBrowserSupport() ;
		URL url ;
		try {
			url = new URL("file://" + indexHTML) ;
		} catch (MalformedURLException e) {
			log.error("Failed to create url for indexHtml: " + indexHTML, e) ;
			return ;
		}
		IWebBrowser browser ;
		try {
			browser = browserSupport
					.createBrowser(IWorkbenchBrowserSupport.AS_EXTERNAL, null, 
							"SVEditor HTML Docsl", "SVEditor HTML docs") ;
			browser.openURL(url) ;
		} catch (PartInitException e) {
			log.error("Failed to open browser", e) ; 
			return ;
		}
	}
	

}

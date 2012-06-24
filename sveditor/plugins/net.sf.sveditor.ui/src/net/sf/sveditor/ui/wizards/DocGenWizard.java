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

import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.DocModel;
import net.sf.sveditor.core.docs.DocModelFactory;
import net.sf.sveditor.core.docs.IDocWriter;
import net.sf.sveditor.core.docs.html.HTMLDocWriter;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard ;
import org.eclipse.ui.IWorkbench;

public class DocGenWizard extends Wizard {
	
	DocGenSelectPkgsWizardPage fSelectPkgsPage ;
	DocGenBasicOptionsWizardPage fBasicOptionsPage ;

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
			// FIXME: Auto-generated catch block
			e.printStackTrace(); } catch (InterruptedException e) { // FIXME: Auto-generated catch block
			e.printStackTrace();
		}
		return true ;
	}

	public void init(IWorkbench workbench) {
		
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
		return fSelectPkgsPage.hasSelection() ;
	}

	@Override
	public boolean performCancel() {
		return super.performCancel() ;
	}

	private void performOperation(DocGenConfig cfg, IProgressMonitor monitor) {
		monitor.beginTask("Generating documentation", 10) ;
		DocModelFactory factory = new DocModelFactory() ;
		DocModel model = factory.build(cfg) ;
		IDocWriter writer = new HTMLDocWriter() ;
		writer.write(cfg, model) ;
		for(int i=0 ; i < 10 ; i++) {
			try {
				Thread.sleep(100) ;
			} catch (InterruptedException e) {
				// FIXME: Auto-generated catch block
				e.printStackTrace();
			}
			monitor.worked(1) ;
		}
		monitor.done() ;
	}
	

}

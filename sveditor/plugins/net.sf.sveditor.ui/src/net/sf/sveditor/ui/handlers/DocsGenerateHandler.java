/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.ui.handlers;

import net.sf.sveditor.ui.wizards.DocGenWizard;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandlerListener;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;

public class DocsGenerateHandler implements IHandler {

	public void addHandlerListener(IHandlerListener handlerListener) {
	}

	public void dispose() {
	}

	public Object execute(ExecutionEvent event) throws ExecutionException {
		IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindow(event) ;
		
		DocGenWizard wizard = new DocGenWizard() ;
		wizard.init(window.getWorkbench()) ;
		
		WizardDialog dialog = new WizardDialog(window.getShell(), wizard) ;
		dialog.open();
		
		return null;
	}

	public boolean isEnabled() {
		return true ;
	}

	public boolean isHandled() {
		return true ;
	}

	public void removeHandlerListener(IHandlerListener handlerListener) {
	}

}

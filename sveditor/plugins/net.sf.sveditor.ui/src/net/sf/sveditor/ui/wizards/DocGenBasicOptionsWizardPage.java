/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

package net.sf.sveditor.ui.wizards;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class DocGenBasicOptionsWizardPage extends WizardPage {
	
	private DirectoryDialog fDirDialog ;
	private Text fDirText ;

	public String getOutputDir() {
		return fDirText.getText() ;
	}

	protected DocGenBasicOptionsWizardPage() {
		super("Basic Options", "Basic Options", SVUiPlugin.getImageDescriptor("/icons/wizards/ndoc_wiz.png")) ;
	}

	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL) ;
		final GridLayout gridLayout = new GridLayout() ;
		gridLayout.numColumns = 1 ;
		container.setLayout(gridLayout) ;
		setControl(container) ;
		
		createLabel(container) ;
		createDirectoryField(container) ;
		
	}
	private void createLabel(Composite container) {
		final Label label = new Label(container, SWT.NONE) ; 
		final GridData gridData = new GridData() ;
		gridData.horizontalSpan = 1 ;
		label.setLayoutData(gridData) ;
		label.setText( "Select output directory for the documentation" ) ;
	}
	
	private void createDirectoryField(Composite parent) {
		
		Group group = new Group(parent, SWT.NONE); 
		group.setText("Output directory") ;
		group.setLayoutData(new GridData(GridData.FILL_HORIZONTAL)) ;
		GridLayout gl = new GridLayout() ;
		gl.numColumns = 2 ;
		group.setLayout(gl) ;
		
		fDirText = new Text(group, SWT.NONE) ; 
		fDirText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL)) ;
		fDirText.setEditable(false) ; // TODO: allow it to be edited. should then also check validity
		
		fDirDialog = new DirectoryDialog(parent.getShell(), SWT.OPEN ) ; 
		Button button = new Button(group, SWT.PUSH) ;
		button.setText("B&rowse") ;
		button.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				String dir = fDirDialog.open() ;
				if(dir != null && !dir.isEmpty()) {
					fDirText.setText(dir) ;
					setPageComplete(!dir.isEmpty()) ;
				}
			}
			public void widgetDefaultSelected(SelectionEvent e) { }
		}) ;
		
	}

}

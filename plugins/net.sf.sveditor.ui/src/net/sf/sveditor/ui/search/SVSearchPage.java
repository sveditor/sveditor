/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.search;

import org.eclipse.jface.dialogs.DialogPage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.search.ui.ISearchPage;
import org.eclipse.search.ui.ISearchPageContainer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

public class SVSearchPage extends DialogPage implements ISearchPage {

	public SVSearchPage() {
		// TODO Auto-generated constructor stub
	}

	public SVSearchPage(String title) {
		super(title);
		// TODO Auto-generated constructor stub
	}

	public SVSearchPage(String title, ImageDescriptor image) {
		super(title, image);
		// TODO Auto-generated constructor stub
	}

	public boolean performAction() {
	
		// TODO Auto-generated method stub
		return false;
	}

	public void setContainer(ISearchPageContainer container) {
		// TODO Auto-generated method stub


	}

	public void createControl(Composite parent) {
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());
		
		Label l = new Label(c, SWT.NONE);
		l.setText("Label Text");
		
		setControl(c);
	}

}

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


package net.sf.sveditor.ui.wizards;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindContentAssistNameMatcher;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.SelectionStatusDialog;

public class BrowseClasses extends SelectionStatusDialog 
	implements IStructuredContentProvider, ILabelProvider {
	
	private Text					fClassName;
	private String					fClassNameStr;
	private boolean					fModifyInProgress;
	
	private ListViewer				fClassList;
	private ISVDBIndexIterator		fIndexIt;
	private List<SVDBItem>			fProposals;
	
	public BrowseClasses(
			Shell 					shell,
			ISVDBIndexIterator		index_it) {
		super(shell);
		fIndexIt = index_it;
		fProposals = new ArrayList<SVDBItem>();
	}
	
	@Override
	protected Control createDialogArea(Composite parent) {
		Label l;
		
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());
		
		Composite name_c = new Composite(c, SWT.NONE);
		name_c.setLayout(new GridLayout(2, false));
		l = new Label(name_c, SWT.NONE);
		l.setText("Name:");
		
		fClassName = new Text(name_c, SWT.BORDER);
		fClassName.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fClassName.addModifyListener(new ModifyListener() {
			
			public void modifyText(ModifyEvent e) {
				fClassNameStr = fClassName.getText();
				if (!fModifyInProgress) {
					updateProposals();
				}
			}
		});
		
		fClassList = new ListViewer(c);
		fClassList.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fClassList.setContentProvider(this);
		fClassList.setInput(fProposals);
		

		return c;
	}
	
	private void updateProposals() {
		SVDBFindByName finder = new SVDBFindByName(fIndexIt, 
				new SVDBFindContentAssistNameMatcher());
		List<SVDBItem> proposals = null;
		
		fProposals.clear();
		if (!fClassNameStr.equals("")) { 
			proposals = finder.find(fClassNameStr, SVDBItemType.Class);
			fProposals.addAll(proposals);
		}
		fClassList.refresh();
	}

	@Override
	protected void computeResult() {
		// TODO Auto-generated method stub
		
	}

	// ContentProvider implementation
	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

	public Object[] getElements(Object inputElement) {
		return fProposals.toArray();
	}

	// LabelProvider implementation
	public Image getImage(Object element) {
		return null;
	}

	public String getText(Object element) {
		return ((SVDBItem)element).getName();
	}

	public void addListener(ILabelProviderListener listener) {}
	public void removeListener(ILabelProviderListener listener) {}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

}

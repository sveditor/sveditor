package net.sf.sveditor.ui.views;

import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.MessagePage;
import org.eclipse.ui.part.PageBook;
import org.eclipse.ui.part.ViewPart;

public class SVHierarchyView extends ViewPart {
	
	private TreeViewer				fClassTree;
	private ListViewer				fMemberList;
	private SVTreeLabelProvider		fLabelProvider;
	private SVDBModIfcClassDecl		fSelection;
	private PageBook				fPageBook;
	private MessagePage				fNoSelPage;

	@Override
	public void createPartControl(Composite parent) {

		/*
		fPageBook = new PageBook(parent, SWT.NONE);
		
		fNoSelPage = new MessagePage();
		fNoSelPage.setMessage("No current selection...");
		 */
		
		SashForm sash = new SashForm(parent, SWT.VERTICAL);
		
		fLabelProvider = new SVTreeLabelProvider();
		
		fClassTree = new TreeViewer(sash);
		fClassTree.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fClassTree.setLabelProvider(fLabelProvider);
		

		sash.setLayoutData(
				new GridData(SWT.FILL, SWT.CENTER, true, false));

		fMemberList = new ListViewer(sash);
		fMemberList.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fMemberList.setLabelProvider(fLabelProvider);
	}

	@Override
	public void setFocus() {}
}



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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBIndexListIterator;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.search.SVDBSearchSpecification;
import net.sf.sveditor.core.db.search.SVDBSearchType;
import net.sf.sveditor.core.db.search.SVDBSearchUsage;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.DialogPage;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.search.ui.ISearchPage;
import org.eclipse.search.ui.ISearchPageContainer;
import org.eclipse.search.ui.ISearchQuery;
import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkingSet;

public class SVSearchPage extends DialogPage implements ISearchPage {
	
	private Combo					fSearchExprCombo;
	private Button					fCaseSensitiveButton;
	private Button					fSearchForTypeButton;
	private Button					fSearchForMethodButton;
	private Button					fSearchForPackageButton;
	private Button					fSearchForFieldButton;
	private ISearchPageContainer 	fContainer;
	private Button 					fLimitToDeclarationsButton;
	private Button 					fLimitToReferencesButton;
	private Button 					fLimitToAllButton;
	private LogHandle				fLog;
	
	private List<SearchSettings>	fSearchHistory;
	private SearchSettings			fCurrentSearch;
	
	private static final String		PAGE_NAME = "SvSearchPage";
	
	private class SearchSettings {
		public String					fSearchExpr;
		public SVDBSearchType			fSearchFor;
		public SVDBSearchUsage			fLimitTo;
		public boolean					fCaseSensitive;
		
		public SearchSettings() {
			fSearchExpr = "";
			fSearchFor = SVDBSearchType.Type;
			fLimitTo = SVDBSearchUsage.Declaration;
			fCaseSensitive = false;
		}
		
		public void store(IDialogSettings s) {
			s.put(PREF_CASE_SENSITIVE, fCaseSensitive);
			s.put(PREF_SEARCH_FOR, fSearchFor.name());
			s.put(PREF_LIMIT_TO, fLimitTo.name());
			s.put(PREF_PATTERN, fSearchExpr);
		}
		
		public void load(IDialogSettings s) {
			fCaseSensitive = s.getBoolean(PREF_CASE_SENSITIVE);
			
			String search_for = s.get(PREF_SEARCH_FOR);
			if (search_for == null) {
				search_for = "";
			}
			if (search_for.equals(SVDBSearchType.Type.name())) {
				fSearchFor = SVDBSearchType.Type;
			} else if (search_for.equals(SVDBSearchType.Method.name())) {
				fSearchFor = SVDBSearchType.Method;
			} else if (search_for.equals(SVDBSearchType.Package.name())) {
				fSearchFor = SVDBSearchType.Package;
			} else if (search_for.equals(SVDBSearchType.Field.name())) {
				fSearchFor = SVDBSearchType.Field;
			} else {
				fSearchFor = SVDBSearchType.Type;
			}
			
			String limit_to = s.get(PREF_LIMIT_TO);
			if (limit_to == null) {
				limit_to = "";
			}
			if (limit_to.equals(SVDBSearchUsage.Declaration.name())) {
				fLimitTo = SVDBSearchUsage.Declaration;
			} else if (limit_to.equals(SVDBSearchUsage.Reference.name())) {
				fLimitTo = SVDBSearchUsage.Reference;
			} else if (limit_to.equals(SVDBSearchUsage.All.name())) {
				fLimitTo = SVDBSearchUsage.All;
			} else {
				fLimitTo = SVDBSearchUsage.Declaration;
			}
			
			fSearchExpr = s.get(PREF_PATTERN);
		}
		
		// Applies these settings to the buttons
		public void apply() {
			fCaseSensitiveButton.setSelection(fCaseSensitive);
			fSearchExprCombo.setText(fSearchExpr);
			
			fSearchForTypeButton.setSelection(false);
			fSearchForMethodButton.setSelection(false);
			fSearchForPackageButton.setSelection(false);
			fSearchForFieldButton.setSelection(false);
			switch (fSearchFor) {
				case Type:		fSearchForTypeButton.setSelection(true); break;
				case Field:		fSearchForFieldButton.setSelection(true); break;
				case Method:	fSearchForMethodButton.setSelection(true); break;
				case Package:	fSearchForPackageButton.setSelection(true); break; 
			}
			
			fLimitToDeclarationsButton.setSelection(false);
			fLimitToReferencesButton.setSelection(false);
			fLimitToAllButton.setSelection(false);
			switch (fLimitTo) {
				case Declaration: fLimitToDeclarationsButton.setSelection(true); break;
				case Reference: fLimitToReferencesButton.setSelection(true); break;
				case All: fLimitToAllButton.setSelection(true); break;
			}
		}
		
		public SearchSettings duplicate() {
			SearchSettings ret = new SearchSettings();
			ret.fCaseSensitive = fCaseSensitive;
			ret.fLimitTo = fLimitTo;
			ret.fSearchExpr = fSearchExpr;
			ret.fSearchFor = fSearchFor;
			
			return ret;
		}
		
		public boolean equals(Object other) {
			if (other instanceof SearchSettings) {
				SearchSettings s = (SearchSettings)other;
				return (s.fCaseSensitive == fCaseSensitive) &&
					(s.fLimitTo == fLimitTo) &&
					(s.fSearchExpr.equals(fSearchExpr)) &&
					(s.fSearchFor == fSearchFor);
			} else {
				return false;
			}
		}
	}

	/**
	 * @wbp.parser.constructor
	 */
	public SVSearchPage() {
		super();
		fSearchHistory = new ArrayList<SVSearchPage.SearchSettings>();
		fCurrentSearch = new SearchSettings();
		fLog = LogFactory.getLogHandle("SVSearchPage");
	}

	public SVSearchPage(String title) {
		super(title);
		// TODO Auto-generated constructor stub
	}

	public SVSearchPage(String title, ImageDescriptor image) {
		super(title, image);
		// TODO Auto-generated constructor stub
	}
	
	private ISearchQuery createQuery() {
		// Determine the context
		
		// Construct the search specification
		SVDBSearchSpecification spec = new SVDBSearchSpecification(
				fCurrentSearch.fSearchExpr.trim(),
				fCurrentSearch.fCaseSensitive,
				false);
		spec.setSearchType(fCurrentSearch.fSearchFor);
		spec.setSearchUsage(fCurrentSearch.fLimitTo);
		
		SVDBIndexListIterator search_ctxt = new SVDBIndexListIterator();
		switch (fContainer.getSelectedScope()) {
			case ISearchPageContainer.SELECTED_PROJECTS_SCOPE: {
				IWorkspace ws = ResourcesPlugin.getWorkspace();
				SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
				
				for (String pn : fContainer.getSelectedProjectNames()) {
					IProject p = ws.getRoot().getProject(pn);
					SVDBProjectData p_data = mgr.getProjectData(p);
					if (p_data != null) {
						ISVDBIndexIterator it = p_data.getProjectIndexMgr();
						// TODO: handle filtering external vs internal paths
						search_ctxt.addIndexIterator(it);
					}
				}
				} break;
				
			case ISearchPageContainer.WORKSPACE_SCOPE: {
				IWorkspace ws = ResourcesPlugin.getWorkspace();
				SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
				
				for (IProject p : ws.getRoot().getProjects()) {
					SVDBProjectData p_data = mgr.getProjectData(p);
					if (p_data != null) {
						ISVDBIndexIterator it = p_data.getProjectIndexMgr();
						// TODO: handle filtering external vs internal paths
						search_ctxt.addIndexIterator(it);
					}
				}
				} break;
				
			case ISearchPageContainer.WORKING_SET_SCOPE: {
				for (IWorkingSet set : fContainer.getSelectedWorkingSets()) {
					SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
					for (IAdaptable adapter : set.getElements()) {
						Object project_o = adapter.getAdapter(IProject.class);
						if (project_o != null) {
							IProject project = (IProject)project_o;
							
							SVDBProjectData p_data = mgr.getProjectData(project);
							if (p_data != null) {
								ISVDBIndexIterator it = p_data.getProjectIndexMgr();
								// TODO: handle filtering external vs internal paths
								search_ctxt.addIndexIterator(it);
							}
						}
					}
				}
				} break;
				
			case ISearchPageContainer.SELECTION_SCOPE: {
				// TODO: Selection scope not supported
				fLog.error("Searching the selected resource is not supported");
				ISelection sel = fContainer.getSelection();
				if (sel instanceof IStructuredSelection) {
					IStructuredSelection ss = (IStructuredSelection)sel;
					for (Object sel_o : ss.toList()) {
						if (sel_o instanceof IProject) {
							
						} else if (sel_o instanceof IFile) {
							
						}
					}
				}
				} break;
		}
		
		return new SVSearchQuery(search_ctxt, spec);
	}

	public boolean performAction() {
		// Save the current dialog settings
		saveSettings(true);
		try {
			NewSearchUI.runQueryInBackground(createQuery());
		} catch (Exception e) {
			e.printStackTrace();
			ErrorDialog.openError(getShell(), "Problem Searching", "Problem Searching", Status.CANCEL_STATUS);
			return false;
		}
		return true;
	}
	
	@Override
	public void dispose() {
		super.dispose();
	}

	public void setContainer(ISearchPageContainer container) {
		fContainer = container;
		// enable initially
		fContainer.setPerformActionEnabled(true);
	}
	
	public void createControl(Composite parent) {
		Composite c = new Composite(parent, SWT.NONE);
		
		setControl(c);
		c.setLayout(new GridLayout(1, false));
		
		Composite composite = new Composite(c, SWT.NONE);
		composite.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1));
		composite.setLayout(new GridLayout(2, false));
		
		fSearchExprCombo = new Combo(composite, SWT.NONE);
		fSearchExprCombo.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1));
		fSearchExprCombo.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fCurrentSearch.fSearchExpr = fSearchExprCombo.getText();
			}
		});
		fSearchExprCombo.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				fCurrentSearch = fSearchHistory.get(fSearchExprCombo.getSelectionIndex()).duplicate();
				fCurrentSearch.apply();
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		fCaseSensitiveButton = new Button(composite, SWT.CHECK);
		fCaseSensitiveButton.setText("Case Sensitive");
		fCaseSensitiveButton.addSelectionListener(prvButtonSelectionListener);
		
		Composite composite_1 = new Composite(c, SWT.NONE);
		composite_1.setLayout(new GridLayout(2, true));
		composite_1.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1));
		
		Group grpSearchFor = new Group(composite_1, SWT.NONE);
		grpSearchFor.setText("Search For");
		grpSearchFor.setLayout(new GridLayout(2, true));
		GridData gd_grpSearchFor = new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1);
		gd_grpSearchFor.widthHint = 287;
		grpSearchFor.setLayoutData(gd_grpSearchFor);
		
		fSearchForTypeButton = new Button(grpSearchFor, SWT.RADIO);
		fSearchForTypeButton.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, true, false, 1, 1));
		fSearchForTypeButton.setText("Type");
		fSearchForTypeButton.addSelectionListener(prvButtonSelectionListener);
		
		fSearchForMethodButton = new Button(grpSearchFor, SWT.RADIO);
		fSearchForMethodButton.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, true, false, 1, 1));
		fSearchForMethodButton.setText("Method");
		fSearchForMethodButton.addSelectionListener(prvButtonSelectionListener);
		
		fSearchForPackageButton = new Button(grpSearchFor, SWT.RADIO);
		fSearchForPackageButton.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, true, false, 1, 1));
		fSearchForPackageButton.setText("Package");
		fSearchForPackageButton.addSelectionListener(prvButtonSelectionListener);
		// new Label(grpSearchFor, SWT.NONE);
		
		fSearchForFieldButton = new Button(grpSearchFor, SWT.RADIO);
		fSearchForFieldButton.setLayoutData(new GridData(SWT.LEFT, SWT.FILL, true, true, 1, 1));
		fSearchForFieldButton.setText("Field");
		fSearchForFieldButton.addSelectionListener(prvButtonSelectionListener);
		// new Label(grpSearchFor, SWT.NONE);
		
		Group grpLimitTo = new Group(composite_1, SWT.NONE);
		grpLimitTo.setText("Limit To");
		grpLimitTo.setLayout(new GridLayout(1, false));
		GridData gd_grpLimitTo = new GridData(SWT.FILL, SWT.FILL, true, true, 1, 1);
		gd_grpLimitTo.widthHint = 288;
		grpLimitTo.setLayoutData(gd_grpLimitTo);
		
		fLimitToDeclarationsButton = new Button(grpLimitTo, SWT.RADIO);
		fLimitToDeclarationsButton.setText("Declarations");
		fLimitToDeclarationsButton.addSelectionListener(prvButtonSelectionListener);
		
		fLimitToReferencesButton = new Button(grpLimitTo, SWT.RADIO);
		fLimitToReferencesButton.setText("References");
		fLimitToReferencesButton.addSelectionListener(prvButtonSelectionListener);
		fLimitToReferencesButton.setEnabled(false); // TODO: just for now
		
		fLimitToAllButton = new Button(grpLimitTo, SWT.RADIO);
		fLimitToAllButton.setText("All");
		fLimitToAllButton.addSelectionListener(prvButtonSelectionListener);
		fLimitToAllButton.setEnabled(false); // TODO: just for now
		
		setControl(c);

		/*
		Group grpSearchIn = new Group(c, SWT.NONE);
		grpSearchIn.setText("Search In");
		grpSearchIn.setLayout(new GridLayout(2, false));
		grpSearchIn.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1));
		
		Button btnSources = new Button(grpSearchIn, SWT.CHECK);
		btnSources.setText("Sources");
		
		Button btnReferencedLibraries = new Button(grpSearchIn, SWT.CHECK);
		btnReferencedLibraries.setText("Referenced Libraries");
		 */

		// Load the stored preferences
		loadSettings();
	}
	
	private SelectionListener prvButtonSelectionListener = new SelectionListener() {
		
		public void widgetSelected(SelectionEvent e) {
			if (e.getSource() == fCaseSensitiveButton) {
				fCurrentSearch.fCaseSensitive = fCaseSensitiveButton.getSelection();
			}
			
			if (e.getSource() == fSearchForTypeButton) {
				fCurrentSearch.fSearchFor = SVDBSearchType.Type;
			}
			if (e.getSource() == fSearchForMethodButton) {
				fCurrentSearch.fSearchFor = SVDBSearchType.Method;
			}
			if (e.getSource() == fSearchForPackageButton) {
				fCurrentSearch.fSearchFor = SVDBSearchType.Package;
			}
			if (e.getSource() == fSearchForFieldButton) {
				fCurrentSearch.fSearchFor = SVDBSearchType.Field;
			}
			
			if (e.getSource() == fLimitToDeclarationsButton) {
				fCurrentSearch.fLimitTo = SVDBSearchUsage.Declaration;
			}
			if (e.getSource() == fLimitToReferencesButton) {
				fCurrentSearch.fLimitTo = SVDBSearchUsage.Reference;
			}
			if (e.getSource() == fLimitToAllButton) {
				fCurrentSearch.fLimitTo = SVDBSearchUsage.All;
			}
		}
		
		public void widgetDefaultSelected(SelectionEvent e) {}
	};
	
	private static final String						PREF_CASE_SENSITIVE = "CASE_SENSITIVE";
	private static final String						PREF_SEARCH_FOR = "SEARCH_FOR";
	private static final String						PREF_LIMIT_TO = "LIMIT_TO";
	private static final int						HISTORY_MAX_SIZE = 12;
	private static final String						PREF_HISTORY_SIZE = "HISTORY_SIZE";
	private static final String						PREF_HISTORY = "HISTORY";
	private static final String						PREF_PATTERN = "PATTERN";
	
	private void saveSettings(boolean on_search) {
		IDialogSettings s = 
			SVUiPlugin.getDefault().getDialogSettingsSection(PAGE_NAME);
		
		List<SearchSettings> items = new ArrayList<SVSearchPage.SearchSettings>();
		items.addAll(fSearchHistory);
		
		int current_idx = -1;
		for (int i=0; i<items.size(); i++) {
			SearchSettings setting = items.get(i);
			if (setting.fSearchExpr.equals(fCurrentSearch.fSearchExpr)) {
				current_idx = i;
			}
		}
		if (current_idx == -1) {
			if (on_search) {
				items.add(0, fCurrentSearch);
			}
		} else {
			if (on_search) {
				// Move this item to the head of the list
				items.remove(current_idx);
				items.add(0, fCurrentSearch);
			}
		}

		int history_size = Math.min(HISTORY_MAX_SIZE, items.size());
		s.put(PREF_HISTORY_SIZE, history_size);
		for (int i=0; i<history_size; i++) {
			IDialogSettings hist_setting = s.addNewSection(PREF_HISTORY + i);
			items.get(i).store(hist_setting);
		}
	}
	
	private void loadSettings() {
		IDialogSettings s = 
			SVUiPlugin.getDefault().getDialogSettingsSection(PAGE_NAME);
		
		fSearchExprCombo.removeAll();
		if (s.get(PREF_HISTORY_SIZE) != null) {
			int history_size = s.getInt(PREF_HISTORY_SIZE);
			if (history_size > 0) {
				fSearchHistory.clear();
				for (int i=0; i<history_size; i++) {
					IDialogSettings history_setting = s.getSection(PREF_HISTORY + i);
					SearchSettings setting = new SearchSettings();
					setting.load(history_setting);
					fSearchHistory.add(setting);
					fSearchExprCombo.add(setting.fSearchExpr);
				}
				fSearchExprCombo.select(0);
				fCurrentSearch = fSearchHistory.get(0).duplicate();
			}
		}
		fCurrentSearch.apply();
	}
}

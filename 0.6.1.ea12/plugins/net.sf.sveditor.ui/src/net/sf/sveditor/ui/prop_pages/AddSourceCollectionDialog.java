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


package net.sf.sveditor.ui.prop_pages;


import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.ui.WorkspaceFileDialog;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

public class AddSourceCollectionDialog extends Dialog {
	private Text				fPath;
	private boolean				fUseDefaults = true;
	private Text				fIncludes;
	private String				fIncludeStr;
	private Text				fExcludes;
	private String				fExcludeStr;
	private String				fPathStr;
	
	public AddSourceCollectionDialog(Shell shell) {
		super(shell);
	}
	
	public void setBase(String path) {
		fPathStr = path;
	}
	
	public String getBase() {
		return fPathStr;
	}
	
	public void setUseDefaultPattern(boolean use) {
		fUseDefaults = use;
	}
	
	public boolean getUseDefaultPattern() {
		return fUseDefaults;
	}
	
	public void setIncludes(String inc) {
		fIncludeStr = inc;
	}
	
	public String getIncludes() {
		return fIncludeStr;
	}
	
	public void setExcludes(String exc) {
		fExcludeStr = exc;
	}
	
	public String getExcludes() {
		return fExcludeStr;
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);
		
		frame.setLayout(new GridLayout(2, false));
		
		Composite entry_c = new Composite(frame, SWT.NONE);
		entry_c.setLayout(new GridLayout(1, true));
		entry_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		GridData gd;
		
		Group g;
		
		g = new Group(entry_c, SWT.BORDER);
		g.setText("Base Path");
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.widthHint = 250;
		g.setLayout(new GridLayout(1, true));
		g.setLayoutData(gd);
		fPath = new Text(g, SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.widthHint = 250;
		fPath.setLayoutData(gd);
		fPath.addModifyListener(new ModifyListener(){
			public void modifyText(ModifyEvent e) {
				fPathStr = fPath.getText();
			}
		});
		
		if (fPathStr != null) {
			fPath.setText(fPathStr);
		}
		
		Composite pattern_group = new Composite(entry_c, SWT.NONE);
		pattern_group.setLayout(new GridLayout(2, false));
		pattern_group.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		Button use_default = new Button(pattern_group, SWT.CHECK);
		use_default.setSelection(fUseDefaults);
		use_default.addSelectionListener(new SelectionListener(){
		
			public void widgetSelected(SelectionEvent e) {
				fUseDefaults = ((Button)e.getSource()).getSelection();
				
				if (fUseDefaults) {
					fIncludes.setEnabled(true);
					fExcludes.setEnabled(true);
					// Ensure the defaults lists have default content
					fIncludes.setText(SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes());
					fExcludes.setText(SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes());
				}
				
				fIncludes.setEditable(!fUseDefaults);
				fIncludes.setEnabled(!fUseDefaults);
				fExcludes.setEditable(!fUseDefaults);
				fExcludes.setEnabled(!fUseDefaults);
			}
		
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		use_default.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false,
				1, 2));
		
		g = new Group(pattern_group, SWT.NONE);
		g.setText("Include Pattern");
		g.setLayout(new GridLayout(1, true));
		g.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fIncludes = new Text(g, SWT.NONE);
		fIncludes.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		if (fIncludeStr != null) {
			fIncludes.setText(fIncludeStr);
		}
		fIncludes.setEditable(!fUseDefaults);
		fIncludes.setEnabled(!fUseDefaults);
		fIncludes.addSelectionListener(new SelectionListener() {
		
			public void widgetSelected(SelectionEvent e) {
				fIncludeStr = fIncludes.getText();
			}
		
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		g = new Group(pattern_group, SWT.NONE);
		g.setText("Exclude Pattern");
		g.setLayout(new GridLayout(1, true));
		g.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fExcludes = new Text(g, SWT.NONE);
		fExcludes.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		if (fExcludeStr != null) {
			fExcludes.setText(fExcludeStr);
		}
		fExcludes.setEditable(!fUseDefaults);
		fExcludes.setEnabled(!fUseDefaults);
		fExcludes.addSelectionListener(new SelectionListener() {
		
			public void widgetSelected(SelectionEvent e) {
				fExcludeStr = fExcludes.getText();
			}
		
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		Composite button_bar = new Composite(frame, SWT.NONE);
		button_bar.setLayout(new GridLayout(1, true));
		button_bar.setLayoutData(new GridData(SWT.CENTER, SWT.FILL, false, true));
		
		Button add_ws_path = new Button(button_bar, SWT.PUSH);
		add_ws_path.setText("Add Workspace Path");
		add_ws_path.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		
		add_ws_path.addSelectionListener(new SelectionListener() {

			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				WorkspaceFileDialog dlg = new WorkspaceFileDialog(getShell());
				dlg.setSelectFiles(false);
				
				if (dlg.open() == Window.OK) {
					if (dlg.getPath() != null) {
						fPath.setText("${workspace_loc}" + dlg.getPath());
					}
				}
			}
		});
		
		Button add_fs_path = new Button(button_bar, SWT.PUSH);
		add_fs_path.setText("Add Filesystem Path");
		add_fs_path.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		add_fs_path.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				DirectoryDialog dlg = new DirectoryDialog(getShell());
				
				dlg.setText("Select a Directory");
				
				String result = dlg.open();
				
				if (result != null && !result.trim().equals("")) {
					fPath.setText(result);
				}
			}
		});

		return frame;
	}
}

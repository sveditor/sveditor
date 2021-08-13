/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.ui.wizards.new_filelist;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.sveditor.ui.ResourceSelCheckboxMgr;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.SVFileUtils;
import org.sveditor.core.argfile.creator.SVArgFileCreator;
import org.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class NewFileListWizardAddFilesPage extends WizardPage {
	private CheckboxTreeViewer			fTreeView;
	private ResourceSelCheckboxMgr		fCheckMgr;
	private Text						fText;
	private boolean						fOrganizeFiles;
	private Button						fOrganizeFilesButton;
	private boolean						fIncludeFilelists;
	private Button						fIncludeFilelistsButton;
	private Button						fUpdateButton;
	private boolean						fUpdateRequired = true;
	private SVArgFileCreator			fArgFileCreator;
	private ISVDBFileSystemProvider		fFSProvider;
	private Object						fInput;
	private Set<String>					fSVFileExts;
	private ITreeContentProvider		fContentProvider;
	private ILabelProvider				fLabelProvider;
	private String						fPrefix;
	private int							fPrefixSubLen;
	private boolean						fRequireFiles = true;
	
	public NewFileListWizardAddFilesPage(
			ITreeContentProvider		cp,
			ILabelProvider				lp,
			ISVDBFileSystemProvider		fs_provider,
			Object						input) {
		super("Add Files", 
				"Locate SystemVerilog files to populate the filelist", null);
		fContentProvider = cp;
		fLabelProvider = lp;
		
		fFSProvider = fs_provider;
		fInput = input;
		fArgFileCreator = new SVArgFileCreator(fFSProvider);
		fSVFileExts = new HashSet<String>();
		
		for (String ext : SVCorePlugin.getDefault().getDefaultSVExts()) {
			fSVFileExts.add(ext);
		}
	}
	
	public void setRequireFiles(boolean req) {
		fRequireFiles = req;
	}
	
	public void setPrefix(String prefix, int len) {
		fPrefix = prefix;
		fPrefixSubLen = len;
	}
	
	public String getArgFileContent() {
		StringBuilder sb = new StringBuilder();

		if (fOrganizeFiles) {
			for (String incdir : fArgFileCreator.getIncDirs()) {
				if (fPrefix != null) {
					String incdir2 = fPrefix + incdir.substring(fPrefixSubLen);
					incdir = incdir2;
				}
				sb.append("+incdir+" + incdir + "\n");
			}
		}
	
		if (fIncludeFilelists) {
			for (String path : fArgFileCreator.getArgFiles()) {
				if (fPrefix != null) {
					path = fPrefix + path.substring(fPrefixSubLen);
				}
				if (path.endsWith(".F")) {
					sb.append("-F " + path + "\n");
				} else {
					sb.append("-f " + path + "\n");
				}
			}
		}
	
		if (fOrganizeFiles) {
			for (String path : fArgFileCreator.getRootFiles()) {
				if (fPrefix != null) {
					path = fPrefix + path.substring(fPrefixSubLen);
				}
				sb.append(path + "\n");
			}
		} else {
			for (String path : fArgFileCreator.getFiles()) {
				if (fPrefix != null) {
					path = fPrefix + path.substring(fPrefixSubLen);
				}
				sb.append(path + "\n");
			}
		}
		
		return sb.toString();
	}	
	
	public boolean updateRequired() {
		return fUpdateRequired;
	}
	
	public ISVDBFileSystemProvider getFSProvider() {
		return fFSProvider;
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd;
		Label l;
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());
		
		SashForm sash = new SashForm(c, SWT.VERTICAL+SWT.FLAT);
		sash.setSashWidth(4);
		sash.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Group g;
		
		g = new Group(sash, SWT.FLAT);
		g.setText("Source Files to Include");
		g.setLayout(new GridLayout(2, false));
//		g.setLayout(new GridLayout());
		fTreeView = new CheckboxTreeViewer(g);
		fTreeView.setLabelProvider(fLabelProvider);
		fTreeView.setContentProvider(fContentProvider);
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 2;
		fTreeView.getTree().setLayoutData(gd);
		fCheckMgr = new ResourceSelCheckboxMgr(fTreeView) {

			@Override
			protected boolean shouldIncludeInBlockSelection(Object parent, Object elem) {
				if (elem instanceof IFile) {
					String path = ((IFile)elem).getFullPath().toString();
					String ext = SVFileUtils.getPathExt(path);
					
					return (ext != null && fSVFileExts.contains(ext));
				}
				return super.shouldIncludeInBlockSelection(parent, elem);
			}
		};
		fTreeView.addCheckStateListener(fCheckMgr);
		
		fTreeView.setInput(fInput);

		l = new Label(g, SWT.NONE);
		l.setText("Organize Files: ");
		fOrganizeFiles = true;
		fOrganizeFilesButton = new Button(g, SWT.CHECK);
		fOrganizeFilesButton.addSelectionListener(fSelectionListener);
		fOrganizeFilesButton.setSelection(true);
		
		l = new Label(g, SWT.NONE);
		l.setText("Include Filelists: ");
		fIncludeFilelists = false;
		fIncludeFilelistsButton = new Button(g, SWT.CHECK);
		fIncludeFilelistsButton.addSelectionListener(fSelectionListener);
		fIncludeFilelistsButton.setSelection(false);
		
		fUpdateButton = new Button(g, SWT.PUSH);
		fUpdateButton.setText("Compute Filelist");
		fUpdateButton.addSelectionListener(fSelectionListener);
		
		fTreeView.addSelectionChangedListener(new ISelectionChangedListener() {
			
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				Display.getDefault().asyncExec(new Runnable() {
					
					@Override
					public void run() {
						fUpdateRequired = true;
						validate();
					}
				});
			}
		});
		
	
		g = new Group(sash, SWT.FLAT);
		g.setText("Filelist Contents");
		g.setLayout(new GridLayout());
		fText = new Text(g, SWT.NONE+SWT.READ_ONLY+SWT.H_SCROLL+SWT.V_SCROLL);
		fText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
	
		validate();
		
		setControl(c);
	}
	
	private void validate() {
		String msg = null;
		String msg_info = null;
		List<Object> items = fCheckMgr.getCheckedItems();
	
		if (items.size() == 0 && fRequireFiles) {
			if (msg == null) {
				msg = "Select Source Folders and Files";
			}
			fUpdateButton.setEnabled(false);
		} else {
			fUpdateButton.setEnabled(true);
		}
		
		if (fUpdateRequired) {
			msg_info = "Need to Update";
		}
	
		setMessage(null, INFORMATION);
		setMessage(null, WARNING);
		setErrorMessage(null);
		
		if (msg != null) {
			setErrorMessage(msg);
		} else if (msg_info != null) {
			setMessage(msg_info, INFORMATION);
		}
		
		setPageComplete(msg == null && msg_info == null);
	}
	
	public void runUpdateOperation() {
		try {
			List<String> search_paths = new ArrayList<String>();
			for (Object r : fCheckMgr.getCheckedItems()) {
				// We've pre-filtered files here
				if (r instanceof IFile) {
					search_paths.add("${workspace_loc}" + ((IResource)r).getFullPath());
				} else if (r instanceof String) {
					search_paths.add((String)r);
				}
			}
					
			fArgFileCreator.setSearchPaths(search_paths);
			
			getContainer().run(true, true, new IRunnableWithProgress() {

				@Override
				public void run(IProgressMonitor monitor) throws InvocationTargetException,
				InterruptedException {
					SubMonitor subMonitor = SubMonitor.convert(monitor);
					int workremaining = 50;
					
					if (fOrganizeFiles) workremaining = 100;
					
					subMonitor.setWorkRemaining(50);
					
					fArgFileCreator.discover_files(subMonitor.newChild(50));
					
					if (fOrganizeFiles) {
						fArgFileCreator.organize_files(subMonitor.newChild(50));
					}
					
				}
			});
		} catch (InterruptedException ex) {
			ex.printStackTrace();
		} catch (InvocationTargetException ex) {
			ex.printStackTrace();
		} 			
	}
	
	private SelectionListener			fSelectionListener = new SelectionListener() {
		
		@Override
		public void widgetSelected(SelectionEvent e) {
			if (e.widget == fUpdateButton) {
				// TODO: run update

				runUpdateOperation();
				fText.setText(getArgFileContent());
			
				fUpdateRequired = false;
				validate();
			} else if (e.widget == fOrganizeFilesButton) {
				if (fOrganizeFiles != fOrganizeFilesButton.getSelection()) {
					fOrganizeFiles = fOrganizeFilesButton.getSelection();
					fUpdateRequired = true;
				}
				validate();
			} else if (e.widget == fIncludeFilelistsButton) {
				if (fIncludeFilelists != fIncludeFilelistsButton.getSelection()) {
					fIncludeFilelists = fIncludeFilelistsButton.getSelection();
					fUpdateRequired = true;
				}
				
				validate();
			}
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) { }
	};

}

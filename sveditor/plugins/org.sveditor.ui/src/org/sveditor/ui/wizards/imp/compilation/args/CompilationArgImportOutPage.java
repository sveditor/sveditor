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
package org.sveditor.ui.wizards.imp.compilation.args;

import org.sveditor.core.argfile.filter.ArgFileFilterCppFiles;
import org.sveditor.core.argfile.filter.ArgFileFilterDuplicates;
import org.sveditor.core.argfile.filter.ArgFileFilterList;
import org.sveditor.core.argfile.filter.ArgFileFilterOptionsFirst;
import org.sveditor.core.argfile.filter.StringArgFileFilter;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;

public class CompilationArgImportOutPage extends WizardPage {
	
	private String					fSrcText;
	
	private Text					fResultText;
	private String					fResult;
	
	private static final int		ORDER_OPTIONS_FIRST = 0;
	private static final int		FILTER_CPP_FILES = 1;
	private static final int		FILTER_DUPLICATES = 2;
	
	private String					fOptions[] = {
//			"Convert paths in the containing project to relative paths"
			"Order Options First",
			"Remove C++ files",
			"Remove Duplicate Paths/Options",
	};
	
	private boolean					fOptionDefaults[] = {
			false,
			true, // FILTER_CPP_FILES
			true
	};
	
	private CheckboxTableViewer		fOptionViewer;
	
	public CompilationArgImportOutPage() {
		super("Output Settings");
	}
	
	public void setSrcText(String text) {
		fSrcText = text;
		
		if (fResultText != null) {
			updateResultText();
		}
	}
	
	public String getResultText() {
		return fResult;
	}

	public void createControl(Composite parent) {
		SashForm sash = new SashForm(parent, SWT.VERTICAL);
		sash.setLayout(new GridLayout());
		sash.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		Group top = new Group(sash, SWT.BORDER);
		top.setText("Transformation Options");
		top.setLayout(new GridLayout());
		top.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fOptionViewer = CheckboxTableViewer.newCheckList(top, SWT.NONE);
		fOptionViewer.getTable().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fOptionViewer.setContentProvider(new IStructuredContentProvider() {
			public Object[] getElements(Object inputElement) {
				return fOptions;
			}
			
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }
			public void dispose() { }
		});
		fOptionViewer.setLabelProvider(new LabelProvider() {
			public String getText(Object element) {
				return element.toString();
			}
		});
		fOptionViewer.addCheckStateListener(new ICheckStateListener() {
			
			public void checkStateChanged(CheckStateChangedEvent event) {
				updateResultText();
			}
		});
		fOptionViewer.setInput(fOptions);
		
		for (int i=0; i<fOptions.length; i++) {
			fOptionViewer.setChecked(fOptions[i], fOptionDefaults[i]);
		}
		
		Group bottom = new Group(sash, SWT.BORDER);
		bottom.setText("Argument File");
		bottom.setLayout(new GridLayout());
		bottom.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fResultText = new Text(bottom, 
				SWT.MULTI+SWT.V_SCROLL+SWT.H_SCROLL+SWT.READ_ONLY);
		fResultText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		updateResultText();

		setControl(sash);
	}
	
	private void updateResultText() {
		ArgFileFilterList filter = new ArgFileFilterList();
		StringArgFileFilter filter_proc = new StringArgFileFilter();
		
		if (fOptionViewer.getChecked(fOptions[FILTER_CPP_FILES])) {
			filter.addFilter(new ArgFileFilterCppFiles());
		}
		
		if (fOptionViewer.getChecked(fOptions[ORDER_OPTIONS_FIRST])) {
			filter.addFilter(new ArgFileFilterOptionsFirst());
		}
		
		if (fOptionViewer.getChecked(fOptions[FILTER_DUPLICATES])) {
			filter.addFilter(new ArgFileFilterDuplicates());
		}
	
		String input = (fSrcText != null)?fSrcText:"";

		// TODO: Apply filter
		fResult = filter_proc.filter(input, filter);
		
		fResultText.setText(fResult);
	}

}

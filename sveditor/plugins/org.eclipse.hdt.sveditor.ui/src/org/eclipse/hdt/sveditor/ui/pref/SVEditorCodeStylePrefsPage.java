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
package net.sf.sveditor.ui.pref;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.hdt.sveditor.core.XMLTransformUtils;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorCodeStylePrefsPage extends PreferencePage implements
		IWorkbenchPreferencePage {
	
	private Map<String, String>				fOptionValMap;
	private List<String>					fOptionNames;
	private CheckboxTableViewer				fTableViewer;
	private Text							fDescription;

	public SVEditorCodeStylePrefsPage() {
		// TODO Auto-generated constructor stub
	}

	public SVEditorCodeStylePrefsPage(String title) {
		super(title);
	}

	public SVEditorCodeStylePrefsPage(String title, ImageDescriptor image) {
		super(title, image);
	}

	public void init(IWorkbench workbench) {
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		
		fOptionValMap = new HashMap<String, String>();
		fOptionNames = new ArrayList<String>();
		
		fOptionNames.addAll(SVParserConfig.getOptionSet());
		
		String pref = getPreferenceStore().getString(SVEditorPrefsConstants.P_SV_CODE_STYLE_PREFS);
		
		try {
			Map<String, String> map = 
				XMLTransformUtils.xml2Map(pref, "preferences", "preference");
			for (String name : fOptionNames) {
				fOptionValMap.put(name, 
						"" + (map.containsKey(name) && map.get(name).equals("true")));
			}
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	protected Control createContents(Composite parent) {
		Composite	frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout());
		frame.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Group upper_group = new Group(frame, SWT.FLAT);
		upper_group.setLayout(new GridLayout());
		upper_group.setText("&Code Style Options");
		upper_group.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fTableViewer = CheckboxTableViewer.newCheckList(upper_group, SWT.WRAP);

		fTableViewer.getTable().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fTableViewer.setContentProvider(fContentProvider);
		fTableViewer.setLabelProvider(fLabelProvider);
		fTableViewer.addCheckStateListener(new ICheckStateListener() {
			public void checkStateChanged(CheckStateChangedEvent event) {
				fOptionValMap.remove(event.getElement());
				fOptionValMap.put((String)event.getElement(), "" + event.getChecked());
			}
		});
		
		fTableViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				String option = (String)sel.getFirstElement();
				fDescription.setText(SVParserConfig.getDescMap().get(option));
			}
		});
		
		
		Group bottom_group = new Group(frame, SWT.FLAT);
		bottom_group.setText("Description");
		bottom_group.setLayout(new GridLayout());
		bottom_group.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fDescription = new Text(bottom_group, SWT.READ_ONLY+SWT.MULTI+SWT.WRAP);
		fDescription.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fTableViewer.setInput(fOptionNames);
		
		for (Entry<String, String> entry : fOptionValMap.entrySet()) {
			fTableViewer.setChecked(entry.getKey(), entry.getValue().equals("true"));
		}
		
		return frame;
	}
	
	private void applyConfig() {
		
		try {
			String val = XMLTransformUtils.map2Xml(fOptionValMap, 
				"preferences", "preference");
			getPreferenceStore().setValue(SVEditorPrefsConstants.P_SV_CODE_STYLE_PREFS, val);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	protected void performApply() {
		applyConfig();
	}

	@Override
	public boolean performOk() {
		applyConfig();
		return true;
	}

	private IStructuredContentProvider 				fContentProvider = new IStructuredContentProvider() {
		
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }
		
		public void dispose() { }
		
		public Object[] getElements(Object inputElement) {
			return fOptionNames.toArray();
		}
	};
	
	private ILabelProvider						fLabelProvider = new LabelProvider() {

		@Override
		public String getText(Object element) {
			return SVParserConfig.getShortDesc((String)element);
		}
	};
	
}

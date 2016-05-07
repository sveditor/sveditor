package net.sf.sveditor.ui.pref;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.XMLTransformUtils;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.preference.ListEditor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Text;

public class TemplatePropertiesEditor extends ListEditor {
	private Text					fPreview;
	private Button					fModify;
	private List					fList;
	private Map<String, String>		fParamValMap;
	
	public TemplatePropertiesEditor(String name, Composite parent) {
		super(name, "SV Template Properties", parent);
		fParamValMap = new HashMap<String, String>();
	}

	@Override
	protected String createList(String[] items) {
		Map<String, String> content = new HashMap<String, String>();
		for (String item : items) {
			content.put(item, fParamValMap.get(item));
		}
		
		String str = "";
		
		try {
			str = XMLTransformUtils.map2Xml(content, 
				"parameters", "parameter");
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return str;
	}
	
	@Override
	protected String[] parseString(String stringList) {
		Map<String, String> content = null;
		fParamValMap.clear();
		
		if (!stringList.trim().equals("")) {
			try {
				content = XMLTransformUtils.xml2Map(
						new StringInputStream(stringList), "parameters", "parameter");
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		if (content != null) {
			Set<String> keys = content.keySet();
			for (Entry<String, String> e : content.entrySet()) {
				fParamValMap.put(e.getKey(), e.getValue());
			}
			return keys.toArray(new String[keys.size()]);
		} else {
			return new String[0];
		}
	}
	
	@Override
	protected void doLoad() {
		super.doLoad();
		if (fList.getSelectionIndex() == -1 && fList.getItemCount() > 0) {
			fList.select(0);
			listSelected();
		}
	}

	@Override
	protected void doFillIntoGrid(Composite parent, int numColumns) {
		super.doFillIntoGrid(parent, numColumns);
		GridData gd;
		
		Group g = new Group(parent, SWT.NONE);
		g.setText("Preview");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = numColumns-1;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		
		fPreview = new Text(g, SWT.READ_ONLY+SWT.MULTI+SWT.BORDER);
		fPreview.setFont(JFaceResources.getTextFont());
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fPreview.setLayoutData(gd);
		
		fModify = new Button(parent, SWT.PUSH);
		fModify.setText("Modif&y...");
		fModify.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false));
		fModify.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}
			
			public void widgetSelected(SelectionEvent e) {
				modifyPressed();
			}
		});
		
		fList = getListControl(parent);
		fList.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}
			public void widgetSelected(SelectionEvent e) {
				listSelected();
			}
		});
	}
	
	private void listSelected() {
		String val = fParamValMap.get(fList.getItem(fList.getSelectionIndex()));
		if (val != null) {
			fPreview.setText(val);
			fModify.setEnabled(true);
		} else {
			fPreview.setText("");
			fModify.setEnabled(false);
		}
	}
	
	private void modifyPressed() {
		String id = fList.getItem(fList.getSelectionIndex());
		String val = fParamValMap.get(id);
		
		TemplatePropertyDialog prefs = new TemplatePropertyDialog(
				getShell(), SWT.SHEET, new HashSet<String>(), false, "Update Template");
		prefs.setParameterId(id);
		prefs.setValue(val);
		
		if (prefs.open() == Dialog.OK) {
			id = prefs.getParameterId();
			val = prefs.getValue();
			
			fParamValMap.put(id, val);
			fPreview.setText(val);
		} 
	}

	@Override
	protected String getNewInputObject() {
		Set<String> taken_ids = new HashSet<String>();
		taken_ids.addAll(fParamValMap.keySet());
		
		String id = null;
		TemplatePropertyDialog prefs = new TemplatePropertyDialog(
				getShell(), SWT.SHEET, taken_ids, true, "Describe Template");
		
		if (prefs.open() == Dialog.OK) {
			id = prefs.getParameterId();
			String val = prefs.getValue();
			
			fParamValMap.put(id, val);
		} 
		
		return id;
	}
	
}


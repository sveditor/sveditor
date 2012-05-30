package net.sf.sveditor.ui.pref;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.XMLTransformUtils;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.preference.ListEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Text;

public class TemplatePropertiesEditor extends ListEditor {
	private Text					fPreview;
	private List					fList;
	private Map<String, String>		fParamValMap;
	
	public TemplatePropertiesEditor(String name, Composite parent) {
		super(name, "SV Template Properties", parent);
		fParamValMap = new HashMap<String, String>();
	}

	@Override
	protected String createList(String[] items) {
		System.out.println("createList");
		
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
			return keys.toArray(new String[keys.size()]);
		} else {
			return new String[0];
		}
	}
	
	@Override
	protected void doFillIntoGrid(Composite parent, int numColumns) {
		super.doFillIntoGrid(parent, numColumns);
		GridData gd;
		
		Group g = new Group(parent, SWT.NONE);
		g.setText("Preview");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = numColumns;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		
		fPreview = new Text(g, SWT.READ_ONLY+SWT.MULTI+SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fPreview.setLayoutData(gd);
		
		fList = getListControl(parent);
		fList.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}
			
			public void widgetSelected(SelectionEvent e) {
				System.out.println("widgetSelected");
			}
		});
	}

	@Override
	protected String getNewInputObject() {
		AddDirectoryPathDialog prefs = new AddDirectoryPathDialog(getShell(), SWT.SHEET);
		
		String dir = null;
		
		if (prefs.open() == Dialog.OK) {
			dir = prefs.getPath();
		} 
		
		return dir;
	}
	
	
}


package net.sf.sveditor.ui.wizards.templates;

import net.sf.sveditor.svt.core.templates.ITemplateParameterProvider;
import net.sf.sveditor.svt.core.templates.TemplateParameterBase;
import net.sf.sveditor.svt.core.templates.TemplateParameterSet;
import net.sf.sveditor.ui.doc.NDText;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;

public class SVTemplateParametersPage2 extends WizardPage {
	
	private TemplateParametersTreeViewer		fParametersTree;
	private NDText								fParameterInfo;
	private TemplateParameterSet				fParameterSet;
	
	public SVTemplateParametersPage2() {
		super("Parameters");
		
		setDescription("Specify parameter template values");
	}
	
	@Override
	public boolean isPageComplete() {
		return true;
	}
	
	public void setTemplateName(String name) {
		setDescription("Specify parameter template values for \"" + name + "\"");
	}

	public void setParameters(TemplateParameterSet parameters) {
		fParameterSet = parameters;
		if (fParametersTree != null) {
			fParametersTree.setParameters(fParameterSet);
			fParametersTree.setInput(fParameterSet);
		}
	}
	
	public ITemplateParameterProvider getTagProcessor() {
		return fParametersTree.getParameters().getParameterProvider();
	}
	
	private void updateDescription(Object sel) {
		String description = "";
		if (sel instanceof TemplateParameterBase) {
			description = ((TemplateParameterBase)sel).getDescription();
			if (description == null) {
				description = "";
			}
		}

		fParameterInfo.setText(description);
	}
	
	public void createControl(Composite parent) {
		/*
		Group c = new Group(parent, SWT.NONE);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout());
		c.setText("Parameters");
		 */
		SashForm sash = new SashForm(parent, SWT.VERTICAL);

		fParametersTree = new TemplateParametersTreeViewer(sash);
		fParametersTree.getTree().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fParameterInfo = new NDText(sash, SWT.BORDER+SWT.READ_ONLY+SWT.V_SCROLL+SWT.WRAP);
		fParameterInfo.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		fParameterInfo.setJavascriptEnabled(false);
		
		fParametersTree.addSelectionChangedListener(new ISelectionChangedListener() {
			
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
			
				updateDescription(sel.getFirstElement());



			}
		});

		if (fParameterSet != null) {
			setParameters(fParameterSet);
		}
		
		setControl(sash);
	}

}

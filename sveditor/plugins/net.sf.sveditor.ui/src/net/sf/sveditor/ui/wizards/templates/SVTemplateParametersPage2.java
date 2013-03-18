package net.sf.sveditor.ui.wizards.templates;

import net.sf.sveditor.core.templates.ITemplateParameterProvider;
import net.sf.sveditor.core.templates.TemplateParameterBase;
import net.sf.sveditor.core.templates.TemplateParameterSet;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;

public class SVTemplateParametersPage2 extends WizardPage {
	
	private TemplateParametersTreeViewer		fParametersTree;
	private Browser								fParameterInfo;
	private TemplateParameterSet				fParameterSet;
	
	public SVTemplateParametersPage2() {
		super("Parameters");
		
	}
	
	@Override
	public boolean isPageComplete() {
		return true;
	}

	public void setParameters(TemplateParameterSet parameters) {
		fParameterSet = parameters;
		if (fParametersTree != null) {
			fParametersTree.setParameters(fParameterSet);
			fParametersTree.setInput(fParameterSet);
		}
	}
	
	public ITemplateParameterProvider getTagProcessor() {
		return fParameterSet.getParameterProvider();
	}
	
	public void createControl(Composite parent) {
		Group c = new Group(parent, SWT.NONE);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout());
		c.setText("Parameters");

		fParametersTree = new TemplateParametersTreeViewer(c);
		fParametersTree.getTree().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fParameterInfo = new Browser(c, SWT.NONE);
		fParameterInfo.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fParameterInfo.setJavascriptEnabled(false);
		
		fParametersTree.addSelectionChangedListener(new ISelectionChangedListener() {
			
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				
				String description = "";
				if (sel.getFirstElement() instanceof TemplateParameterBase) {
					description = ((TemplateParameterBase)sel.getFirstElement()).getDescription();
					if (description == null) {
						description = "";
					}
				}
				fParameterInfo.setText(description);
			}
		});

		if (fParameterSet != null) {
			setParameters(fParameterSet);
		}
		
		setControl(c);
	}

}

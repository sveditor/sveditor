package net.sf.sveditor.ui.svt.editor;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.widgets.FormToolkit;

public class TemplateSectionPart extends SectionPart {
	
	public TemplateSectionPart(
			Composite 		parent, 
			FormToolkit		tk,
			int				style) {
		super(parent, tk, style);
		
		
		
		Label l = tk.createLabel(getSection(), "Hello");
		
		getSection().setClient(l);
	}

}

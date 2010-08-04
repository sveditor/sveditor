package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.templates.GlobalTemplateVariables;
import org.eclipse.jface.text.templates.TemplateContextType;

public class SVTemplateContextType extends TemplateContextType {

	public SVTemplateContextType() {
		addResolver(new GlobalTemplateVariables.Cursor());
		addResolver(new GlobalTemplateVariables.WordSelection());
		addResolver(new GlobalTemplateVariables.LineSelection());
		addResolver(new GlobalTemplateVariables.Dollar());
		addResolver(new GlobalTemplateVariables.Date());
		addResolver(new GlobalTemplateVariables.Year());
		addResolver(new GlobalTemplateVariables.Time());
		addResolver(new GlobalTemplateVariables.User());
	}

	public SVTemplateContextType(String id) {
		super(id);
		// TODO Auto-generated constructor stub
	}

	public SVTemplateContextType(String id, String name) {
		super(id, name);
		// TODO Auto-generated constructor stub
	}

}

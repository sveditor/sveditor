package net.sf.sveditor.svt.core.templates;

import java.util.List;

public class ExtensionPointTemplateRegistry extends WorkspaceTemplateRegistry {

	@Override
	protected void add_finders(List<AbstractTemplateFinder> finders) {
		super.add_finders(finders);
		finders.add(new ExtensionTemplateFinder());
	}

	
}

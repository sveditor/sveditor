package net.sf.sveditor.svt.core.templates;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogHandle;

public abstract class AbstractTemplateFinder implements ILogLevel {
	protected LogHandle					fLog;
	protected List<TemplateInfo>		fTemplates;
	protected List<TemplateCategory>	fCategories;
	
	public AbstractTemplateFinder() {
		fTemplates = new ArrayList<TemplateInfo>();
		fCategories = new ArrayList<TemplateCategory>();
	}
	
	public abstract void find();
	
	public List<TemplateInfo> getTemplates() {
		return fTemplates;
	}
	
	public List<TemplateCategory> getCategories() {
		return fCategories;
	}
	
	protected void addTemplate(TemplateInfo template) {
		fTemplates.add(template);
	}
	
	protected void addCategory(TemplateCategory category) {
		fCategories.add(category);
	}
	
}

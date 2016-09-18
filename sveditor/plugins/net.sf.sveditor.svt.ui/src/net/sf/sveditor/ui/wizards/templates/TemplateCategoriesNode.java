package net.sf.sveditor.ui.wizards.templates;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.svt.core.templates.TemplateCategory;
import net.sf.sveditor.svt.core.templates.TemplateInfo;
import net.sf.sveditor.svt.core.templates.WorkspaceTemplateRegistry;

public class TemplateCategoriesNode {
	
	private Map<TemplateCategory, List<TemplateInfo>>		fCategoryMap;
	
	public TemplateCategoriesNode() {
		fCategoryMap = new HashMap<TemplateCategory, List<TemplateInfo>>();
	}
	
	public List<TemplateInfo> getTemplates(TemplateCategory category) {
		return fCategoryMap.get(category);
	}
	
	public List<TemplateCategory> getCategories() {
		List<TemplateCategory> ret = new ArrayList<TemplateCategory>();
		
		for (TemplateCategory c : fCategoryMap.keySet()) {
			ret.add(c);
		}
		
		return ret;
	}
	
	public static TemplateCategoriesNode create(WorkspaceTemplateRegistry rgy) {
		TemplateCategoriesNode ret = new TemplateCategoriesNode();
		
		for (TemplateCategory c : rgy.getCategories()) {
			List<TemplateInfo> ti = rgy.getTemplates(c.getId());
			ret.fCategoryMap.put(c, ti);
		}
		
		return ret;
	}

}

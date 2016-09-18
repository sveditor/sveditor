/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.svt.core.templates;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogHandle;

public class TemplateRegistry implements ILogLevel {
	protected static LogHandle						fLog;
	protected List<TemplateCategory>				fCategories;
	protected List<TemplateInfo>					fTemplates;
	protected Map<String, List<TemplateInfo>>		fCategoryMap;
	protected List<IExternalTemplatePathProvider>	fPathProviders;
	
	protected TemplateRegistry() {
		fCategories = new ArrayList<TemplateCategory>();
		fTemplates  = new ArrayList<TemplateInfo>();
		fCategoryMap = new HashMap<String, List<TemplateInfo>>();
		
		fPathProviders = new ArrayList<IExternalTemplatePathProvider>();
		
		load_extensions();
	}
	
	public void addPathProvider(IExternalTemplatePathProvider p) {
		fPathProviders.add(p);
	}
	
	public void clearPathProviders() {
		fPathProviders.clear();
	}
	
	public List<TemplateCategory> getCategories() {
		return fCategories;
	}
	
	public List<String> getCategoryNames() {
		List<String> ret = new ArrayList<String>();
		
		for (TemplateCategory c : fCategories) {
			ret.add(c.getName());
		}
		
		return ret;
	}

	public List<String> getCategoryIDs() {
		List<String> ret = new ArrayList<String>();
		
		for (TemplateCategory c : fCategories) {
			ret.add(c.getId());
		}
		
		return ret;
	}
	
	/**
	 * Get the list of templates associated with the specified category ID
	 * 
	 * @param id
	 * @return
	 */
	public List<TemplateInfo> getTemplates(String id) {
		List<TemplateInfo> ret = new ArrayList<TemplateInfo>();
		if (id == null) {
			id = "";
		}
		
		if (fCategoryMap.containsKey(id)) {
			ret.addAll(fCategoryMap.get(id));
		}
		
		return ret;
	}
	
	public TemplateInfo findTemplate(String id) {
		for (TemplateInfo info : fTemplates) {
			if (info.getId().equals(id)) {
				return info;
			}
		}
		
		return null;
	}
	
	protected void add_finders(List<AbstractTemplateFinder> finders) {
		// Do nothing
	}

	public void load_extensions() {
		fLog.debug(LEVEL_MID, "load_extensions");
		List<AbstractTemplateFinder> template_finders = new ArrayList<AbstractTemplateFinder>();
		fTemplates.clear();
		fCategories.clear();
		fCategoryMap.clear();
	
		add_finders(template_finders);
		
		for (AbstractTemplateFinder f : template_finders) {
			f.find();
			List<TemplateInfo> tmpl_list = f.getTemplates();
			List<TemplateCategory> category_list = f.getCategories();
			
			fTemplates.addAll(tmpl_list);
			for (TemplateCategory new_c : category_list) {
				if (!fCategories.contains(new_c)) {
					fCategories.add(new_c);
				}
			}
		}
		
		// Sort the categories
		for (int i=0; i<fCategories.size(); i++) {
			for (int j=i+1; j<fCategories.size(); j++) {
				TemplateCategory c_i = fCategories.get(i);
				TemplateCategory c_j = fCategories.get(j);
				
				if (c_j.getName().compareTo(c_i.getName()) < 0) {
					fCategories.set(j, c_i);
					fCategories.set(i, c_j);
				}
			}
		}
		
		for (TemplateInfo t : fTemplates) {
			if (t.getCategoryId() == null || t.getCategoryId().trim().equals("")) {
				// Add an 'Other' category
				if (!fCategoryMap.containsKey("net.sf.sveditor.template.category.other")) {
					TemplateCategory c = new TemplateCategory(
							"net.sf.sveditor.template.category.other",
							"Other", "");
					c.setDescription("Category for uncategorized templates");
					t.setCategoryId("net.sf.sveditor.template.category.other");
				}
			}
			if (!fCategoryMap.containsKey(t.getCategoryId())) {
				fCategoryMap.put(t.getCategoryId(), new ArrayList<TemplateInfo>());
			}
			fCategoryMap.get(t.getCategoryId()).add(t);
		}
		
		// Now, sort the templates in each category
		for (Entry<String, List<TemplateInfo>> c : fCategoryMap.entrySet()) {
			List<TemplateInfo> t = c.getValue();
			
			for (int i=0; i<t.size(); i++) {
				for (int j=i+1; j<t.size(); j++) {
					TemplateInfo t_i = t.get(i);
					TemplateInfo t_j = t.get(j);
					
					if (t_j.getName().compareTo(t_i.getName()) < 0) {
						t.set(i, t_j);
						t.set(j, t_i);
					}
				}
			}
		}
	}
}

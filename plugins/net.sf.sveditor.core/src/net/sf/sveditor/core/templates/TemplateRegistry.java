/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.templates;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

public class TemplateRegistry {
	private static TemplateRegistry				fDefault;
	private static LogHandle					fLog;
	private List<TemplateCategory>				fCategories;
	private List<TemplateInfo>					fTemplates;
	private Map<String, List<TemplateInfo>>		fCategoryMap;
	
	static {
		fLog = LogFactory.getLogHandle("MethodologyTemplateRegistry");
	}
	
	public TemplateRegistry() {
		fCategories = new ArrayList<TemplateCategory>();
		fTemplates  = new ArrayList<TemplateInfo>();
		fCategoryMap = new HashMap<String, List<TemplateInfo>>();
		
		load_extensions();
	}
	
	public static TemplateRegistry getDefault() {
		if (fDefault == null) {
			fDefault = new TemplateRegistry();
		}
		return fDefault;
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

	private void load_extensions() {
		IExtensionRegistry ext_rgy = Platform.getExtensionRegistry();
		IExtensionPoint ext_pt = ext_rgy.getExtensionPoint(
				SVCorePlugin.PLUGIN_ID, "SVMethodologyTemplates");
		IExtension ext_list[] = ext_pt.getExtensions();
		
		for (IExtension ext : ext_list) {
			IConfigurationElement ce_l[] = ext.getConfigurationElements();

			for (IConfigurationElement ce : ce_l) {
				String name = ce.getName();
				if (name.equals("methodologyCategory")) {
					addMethodologyCategory(ce);
				} else if (name.equals("methodologyTemplate")) {
					addMethodologyTemplate(ce);
				} else {
					fLog.error("Unknown SVMethodologyTemplate element \"" + 
							name + "\"");
				}
				System.out.println("name=" + name);
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
			if (!fCategoryMap.containsKey(t.getCategoryId())) {
				fCategoryMap.put(t.getCategoryId(), new ArrayList<TemplateInfo>());
			}
			fCategoryMap.get(t.getCategoryId()).add(t);
		}
		
		// Now, sort the templates in each category
		for (Entry<String, List<TemplateInfo>> c : fCategoryMap.entrySet()) {
			List<TemplateInfo> t = c.getValue();
			
			System.out.println("Category \"" + c.getKey() + "\" has " + c.getValue().size());
			
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

	private void addMethodologyCategory(IConfigurationElement ce) {
		String id		= ce.getAttribute("id");
		String name 	= ce.getAttribute("name");
		TemplateCategory c = new TemplateCategory(id, name);
		
		fCategories.add(c);
	}
	
	private void addMethodologyTemplate(IConfigurationElement ce) {
		String id				= ce.getAttribute("id");
		String name				= ce.getAttribute("name");
		String category			= ce.getAttribute("category");
		String description		= "";
		Bundle bundle 			= Platform.getBundle(ce.getContributor().getName());
		
		for (IConfigurationElement ce_c : ce.getChildren()) {
			if (ce_c.getName().equals("description")) {
				description = ce_c.getValue();
			}
		}

		TemplateInfo info = new TemplateInfo(id, name, category, description, 
				new PluginInStreamProvider(bundle));
		fTemplates.add(info);
		
		for (IConfigurationElement ce_c : ce.getChildren()) {
			if (ce_c.getName().equals("templateFiles")) {
				for (IConfigurationElement tmpl : ce_c.getChildren()) {
					String template = tmpl.getAttribute("template");
					String tmpl_name = tmpl.getAttribute("name");
					info.addTemplate(new Tuple<String, String>(template, tmpl_name));
				}
			}
		}
	}
}

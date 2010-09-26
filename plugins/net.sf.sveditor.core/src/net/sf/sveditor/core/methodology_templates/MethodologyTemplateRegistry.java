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


package net.sf.sveditor.core.methodology_templates;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;

public class MethodologyTemplateRegistry {
	private static MethodologyTemplateRegistry			fDefault;
	private static LogHandle							fLog;
	private List<MethodologyCategory>					fCategories;
	private List<MethodologyTemplate>					fTemplates;
	private Map<String, List<MethodologyTemplate>>		fCategoryMap;
	
	static {
		fLog = LogFactory.getLogHandle("MethodologyTemplateRegistry");
	}
	
	public MethodologyTemplateRegistry() {
		fCategories = new ArrayList<MethodologyCategory>();
		fTemplates  = new ArrayList<MethodologyTemplate>();
		fCategoryMap = new HashMap<String, List<MethodologyTemplate>>();
		
		load_extensions();
	}
	
	public static MethodologyTemplateRegistry getDefault() {
		if (fDefault == null) {
			fDefault = new MethodologyTemplateRegistry();
		}
		return fDefault;
	}
	
	public List<String> getCategoryNames() {
		List<String> ret = new ArrayList<String>();
		
		for (MethodologyCategory c : fCategories) {
			ret.add(c.getName());
		}
		
		return ret;
	}

	public List<String> getCategoryIDs() {
		List<String> ret = new ArrayList<String>();
		
		for (MethodologyCategory c : fCategories) {
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
	public List<MethodologyTemplate> getTemplates(String id) {
		List<MethodologyTemplate> ret = new ArrayList<MethodologyTemplate>();
		if (id == null) {
			id = "";
		}
		
		System.out.println("key=\"" + id + "\"");
		if (fCategoryMap.containsKey(id)) {
			System.out.println("    contains");
			ret.addAll(fCategoryMap.get(id));
		}
		
		return ret;
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
				MethodologyCategory c_i = fCategories.get(i);
				MethodologyCategory c_j = fCategories.get(j);
				
				if (c_j.getName().compareTo(c_i.getName()) < 0) {
					fCategories.set(j, c_i);
					fCategories.set(i, c_j);
				}
			}
		}
		
		for (MethodologyTemplate t : fTemplates) {
			if (!fCategoryMap.containsKey(t.getCategoryId())) {
				fCategoryMap.put(t.getCategoryId(), new ArrayList<MethodologyTemplate>());
			}
			fCategoryMap.get(t.getCategoryId()).add(t);
		}
		
		// Now, sort the templates in each category
		for (Entry<String, List<MethodologyTemplate>> c : fCategoryMap.entrySet()) {
			List<MethodologyTemplate> t = c.getValue();
			
			System.out.println("Category \"" + c.getKey() + "\" has " + c.getValue().size());
			
			for (int i=0; i<t.size(); i++) {
				for (int j=i+1; j<t.size(); j++) {
					MethodologyTemplate t_i = t.get(i);
					MethodologyTemplate t_j = t.get(j);
					
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
		MethodologyCategory c = new MethodologyCategory(id, name);
		
		fCategories.add(c);
	}
	
	private void addMethodologyTemplate(IConfigurationElement ce) {
		String id				= ce.getAttribute("id");
		String name				= ce.getAttribute("name");
		String category			= ce.getAttribute("category");
		String templateFile		= ce.getAttribute("templateFile");
		
		if (id != null && name != null && templateFile != null) {
			StringBuilder sb = SVCorePlugin.readResourceFile(ce, "templateFile");
			MethodologyTemplate t = new MethodologyTemplate(id, name, category);
			t.setTemplate(sb.toString());
			fTemplates.add(t);
		}
	}
}

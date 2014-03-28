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

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.Tuple;

public class TemplateInfo {
	private String								fId;
	private String								fName;
	private String								fCategoryId;
	private String								fDescription;
	private List<Tuple<String, String>>			fTemplateList;
	private Map<String, Boolean>				fExecutableMap;
	private TemplateParameterSet				fParameters;
	private String								fGenerateScript;
	private ITemplateInStreamProvider			fStreamProvider;
	private List<TemplateParameterComposite>	fCompositeTemplateTypes;
	
	public TemplateInfo(
			String 						id, 
			String 						name, 
			String 						category_id,
			String						description,
			ITemplateInStreamProvider	stream_provider) {
		fId 			= id;
		fName 			= name;
		fCategoryId 	= (category_id != null)?category_id:"";
		fDescription	= description;
		fTemplateList	= new ArrayList<Tuple<String,String>>();
		fExecutableMap  = new HashMap<String, Boolean>();
		fParameters		= new TemplateParameterSet();
		fStreamProvider = stream_provider;
		fCompositeTemplateTypes = new ArrayList<TemplateParameterComposite>();
	}
	
	public String getId() {
		return fId;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getCategoryId() {
		return fCategoryId;
	}

	public void setCategoryId(String id) {
		fCategoryId = id;
	}

	public void setDescription(String description) {
		fDescription = description;
	}
	public String getDescription() {
		return fDescription;
	}
	
	public List<TemplateParameterComposite> getCompositeTypes() {
		return fCompositeTemplateTypes;
	}
	
	public void addCompositeType(TemplateParameterComposite c) {
		fCompositeTemplateTypes.add(c);
	}
	
	public TemplateParameterComposite findCompositeType(String name) {
		TemplateParameterComposite ret = null;
		
		for (TemplateParameterComposite c : fCompositeTemplateTypes) {
			if (c.getName().equals(name)) {
				ret = c;
				break;
			}
		}
		
		return ret;
	}
	
	/**
	 * Returns a list of the template files
	 * template path / filename
	 * @return
	 */
	public Iterable<Tuple<String, String>> getTemplates() {
		return new Iterable<Tuple<String,String>>() {
			public Iterator<Tuple<String, String>> iterator() {
				return fTemplateList.iterator();
			}
		};
	}
	
	public void addTemplate(String template, String filename) {
		addTemplate(new Tuple<String, String>(template, filename));
	}
	
	public void setExecutable(String path, boolean is_executable) {
		if (fExecutableMap.containsKey(path)) {
			fExecutableMap.remove(path);
		}
		fExecutableMap.put(path, is_executable);
	}
	
	public boolean getExecutable(String path) {
		if (fExecutableMap.containsKey(path)) {
			return fExecutableMap.get(path);
		} else {
			return false;
		}
	}
	
	/**
	 * Adds a tuple: template-path / filename
	 * @param template
	 */
	public void addTemplate(Tuple<String, String> template) {
		fTemplateList.add(template);
	}
	
	public void addParameter(TemplateParameterBase p) {
		fParameters.addParameter(p);
	}
	
	public TemplateParameterSet getParameters() {
		return fParameters;
	}
	
	public InputStream openTemplate(String path) {
		return fStreamProvider.openStream(path);
	}

	public void closeTemplate(InputStream in) {
		fStreamProvider.closeStream(in);
	}

	public void setGenerateScript(String path) {
		fGenerateScript = path;
	}
	
	public String getGenerateScript() {
		return fGenerateScript;
	}
}

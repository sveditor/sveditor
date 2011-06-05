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

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.Tuple;

public class TemplateInfo {
	private String							fId;
	private String							fName;
	private String							fCategoryId;
	private String							fDescription;
	private List<Tuple<String, String>>		fTemplateList;
	private ITemplateInStreamProvider		fStreamProvider;
	
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
		fStreamProvider = stream_provider;
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
	
	public String getDescription() {
		return fDescription;
	}
	
	public Iterable<Tuple<String, String>> getTemplates() {
		return new Iterable<Tuple<String,String>>() {
			public Iterator<Tuple<String, String>> iterator() {
				return fTemplateList.iterator();
			}
		};
	}
	
	public void addTemplate(Tuple<String, String> template) {
		fTemplateList.add(template);
	}
	
	public InputStream openTemplate(String path) {
		return fStreamProvider.openStream(path);
	}

	public void closeTemplate(InputStream in) {
		fStreamProvider.closeStream(in);
	}

}

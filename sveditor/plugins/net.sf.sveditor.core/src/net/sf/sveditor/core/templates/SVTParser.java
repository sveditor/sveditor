package net.sf.sveditor.core.templates;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class SVTParser {
	private Document					fDocument;
	private List<TemplateInfo>			fTemplates;
	private List<TemplateCategory>		fCategories;
	private LogHandle					fLog;
	private ITemplateInStreamProvider	fInProvider;
	private String						fTemplateBase;
	
	
	public SVTParser(
			String						template_base,
			ITemplateInStreamProvider	in_provider) {
		fTemplates = new ArrayList<TemplateInfo>();
		fCategories = new ArrayList<TemplateCategory>();
		fLog = LogFactory.getLogHandle("SVTParser");
		fInProvider = in_provider;
		fTemplateBase = template_base;
	}
	
	public void parse(InputStream in) throws Exception {
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		DocumentBuilder b = f.newDocumentBuilder();
		
		fTemplates.clear();
		fCategories.clear();
		
		b.setErrorHandler(fErrorHandler);
		
		fDocument = b.parse(in);
		
		NodeList sv_template_list = fDocument.getElementsByTagName("sv_template");
		
		if (sv_template_list.getLength() == 0) {
			return;
		}
		
		Element sv_template = (Element)sv_template_list.item(0);
		
		NodeList category_list = sv_template.getElementsByTagName("category");
		for (int i=0; i<category_list.getLength(); i++) {
			addCategory((Element)category_list.item(i));
		}
		
		NodeList template_list = sv_template.getElementsByTagName("template");
		for (int i=0; i<template_list.getLength(); i++) {
			addTemplate((Element)template_list.item(i));
		}

	}
	
	public List<TemplateCategory> getCategories() {
		return fCategories;
	}
	
	public List<TemplateInfo> getTemplates() {
		return fTemplates;
	}
	
	private void addCategory(Element category) {
		String name		= category.getAttribute("name");
		String id		= category.getAttribute("id");
		String parent	= category.getAttribute("parent");
		
		if (parent == null) {
			parent = "";
		}
		
		TemplateCategory c = new TemplateCategory(id, name, parent);
		
		NodeList dl = category.getElementsByTagName("description");
		
		if (dl.getLength() > 0) {
			Element desc = (Element)dl.item(0);
			c.setDescription(desc.getTextContent());
		}
		
		if (!fCategories.contains(c)) {
			fCategories.add(c);
		}
	}
	
	private void addTemplate(Element template) {
		String name 	= template.getAttribute("name");
		String id   	= template.getAttribute("id");
		String category = template.getAttribute("category");
		
		TemplateInfo t = new TemplateInfo(id, name, category, "", fInProvider);
		
		NodeList description = template.getElementsByTagName("description");
		
		if (description.getLength() > 0) {
			Element e = (Element)description.item(0);
			t.setDescription(e.getTextContent());
		}
		
		NodeList files = template.getElementsByTagName("files");
		
		if (files.getLength() > 0) {
			Element e = (Element)files.item(0);
			NodeList file_list = e.getElementsByTagName("file");
			
			for (int i=0; i<file_list.getLength(); i++) {
				Element file = (Element)file_list.item(i);
				String filename = file.getAttribute("name");
				String tmpl_path = file.getAttribute("template");
			
				filename = filename.trim();
				tmpl_path = tmpl_path.trim();
				
				t.addTemplate(fTemplateBase + "/" + tmpl_path, filename);
			}
		}
		
		NodeList parameters = template.getElementsByTagName("parameters");
		
		if (parameters.getLength() > 0) {
			Element e = (Element)parameters.item(0);
			NodeList parameters_list = e.getElementsByTagName("parameter");
			
			for (int i=0; i<parameters_list.getLength(); i++) {
				Element parameter = (Element)parameters_list.item(i);
				
				TemplateParameterType p_type = TemplateParameterType.ParameterType_Id;
				String p_name   = parameter.getAttribute("name");
				String p_type_s = parameter.getAttribute("type");
				String p_dflt   = parameter.getAttribute("default");
				String p_ext    = parameter.getAttribute("extends_from");
				String p_restr  = parameter.getAttribute("restrictions");
				
				if (p_type_s.equals("class")) {
					p_type = TemplateParameterType.ParameterType_Class;
				} else if (p_type_s.equals("id")) {
					p_type = TemplateParameterType.ParameterType_Id;
				} else if (p_type_s.equals("int")) {
					p_type = TemplateParameterType.ParameterType_Int;
				}
				
				TemplateParameter p = new TemplateParameter(
						p_type, p_name, p_dflt, p_ext);
				
				if (p_restr != null && !p_restr.trim().equals("")) {
					String restr[] = p_restr.split(",");
					
					for (String r : restr) {
						r = r.trim();
						p.addValue(r);
					}
				}
				t.addParameter(p);
			}
		}
		
		fTemplates.add(t);
	}

	private ErrorHandler fErrorHandler = new ErrorHandler() {

		public void error(SAXParseException arg0) throws SAXException {
			throw arg0;
		}

		public void fatalError(SAXParseException arg0) throws SAXException {
			throw arg0;
		}

		public void warning(SAXParseException arg0) throws SAXException {}
	};

}

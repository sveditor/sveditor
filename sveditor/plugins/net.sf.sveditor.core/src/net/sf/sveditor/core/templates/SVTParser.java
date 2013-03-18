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
		String genscript = template.getAttribute("genscript");
		
		TemplateInfo t = new TemplateInfo(id, name, category, "", fInProvider);
		
		if (genscript != null && !genscript.trim().equals("")) {
			genscript = fTemplateBase + "/" + genscript;
			
			t.setGenerateScript(genscript);
		}
		
		
		NodeList description = template.getElementsByTagName("description");
		
		if (description.getLength() > 0) {
			Element e = (Element)description.item(0);
			t.setDescription(e.getTextContent());
		}
		
		// First, parse the composite template types
		NodeList compositeTypes = template.getElementsByTagName("compositeTypes");
		
		if (compositeTypes.getLength() > 0) {
			Element e = (Element)compositeTypes.item(0);
			NodeList compositeTypes_list = e.getElementsByTagName("compositeType");
			
			for (int i=0; i<compositeTypes_list.getLength(); i++) {
				Element compositeType = (Element)compositeTypes_list.item(i);
				TemplateParameterComposite composite = parseCompositeType(t, compositeType);
				t.addCompositeType(composite);
			}
		}
		
		NodeList files = template.getElementsByTagName("files");
		
		if (files.getLength() > 0) {
			Element e = (Element)files.item(0);
			NodeList file_list = e.getElementsByTagName("file");
			
			for (int i=0; i<file_list.getLength(); i++) {
				Element file = (Element)file_list.item(i);
				String filename = file.getAttribute("name");
				String tmpl_path = file.getAttribute("template");
				String executable = file.getAttribute("executable");
			
				filename = filename.trim();
				tmpl_path = tmpl_path.trim();
				
				t.addTemplate(fTemplateBase + "/" + tmpl_path, filename);
				t.setExecutable(fTemplateBase + "/" + tmpl_path, 
						(executable != null && executable.equals("true")));
			}
		}
		
		NodeList parameters = template.getElementsByTagName("parameters");
		
		if (parameters.getLength() > 0) {
			Element e = (Element)parameters.item(0);
			NodeList parameters_list = e.getElementsByTagName("parameter");
			
			for (int i=0; i<parameters_list.getLength(); i++) {
				Element parameter = (Element)parameters_list.item(i);
			
				TemplateParameterBase p = parseParameter(t, parameter);
				
				if (p != null) {
					t.addParameter(p);
				}
			}
		}
		
		fTemplates.add(t);
	}
	
	private TemplateParameterComposite parseCompositeType(TemplateInfo t, Element compositeType) {
		TemplateParameterComposite ret = null;
		String description 	= "";
		String name 		= null;
		
		NodeList description_nl = compositeType.getElementsByTagName("description");
		
		if (description_nl.getLength() > 0) {
			Element description_e = (Element)description_nl.item(0);
			description = description_e.getTextContent();
		}
		
		name = compositeType.getAttribute("name");
		
		ret = new TemplateParameterComposite();
		ret.setName(name);
		ret.setDescription(description);

		NodeList parameters_nl = compositeType.getElementsByTagName("parameter");
		
		for (int i=0; i<parameters_nl.getLength(); i++) {
			Element parameter_e = (Element)parameters_nl.item(i);
			TemplateParameterBase p = parseParameter(t, parameter_e);
			
			if (p != null) {
				ret.addParameter(p);
			}
		}
	
		return ret;
	}
	
	private TemplateParameterBase parseParameter(TemplateInfo t, Element parameter) {
		TemplateParameterBase ret = null;
		String name = parameter.getAttribute("name");
		String type = parameter.getAttribute("type");
		
		NodeList desc_n = parameter.getElementsByTagName("description");
		String description = null;
		
		if (desc_n.getLength() > 0) {
			description = desc_n.item(0).getTextContent();
		}
		
		if (type.equals("id") || type.equals("enum")) {
			String p_restr  = parameter.getAttribute("restrictions");
			String p_dflt   = parameter.getAttribute("default");
			TemplateParameterType type_e;
			
			if (type.equals("id")) {
				type_e = TemplateParameterType.ParameterType_Id;
			} else {
				type_e = TemplateParameterType.ParameterType_Enum;
			}
			TemplateParameter p = new TemplateParameter(
					type_e, name, p_dflt, null);

			if (p_restr != null && !p_restr.trim().equals("")) {
				String restr[] = p_restr.split(",");
				
				for (String r : restr) {
					r = r.trim();
					p.addValue(r);
				}
			}
			
			ret = p;
		} else if (type.equals("class")) {
			String p_dflt   = parameter.getAttribute("default");
			String p_ext    = parameter.getAttribute("extends_from");
			ret = new TemplateParameter(
					TemplateParameterType.ParameterType_Class,
					name, p_dflt, p_ext);
		} else if (type.equals("int")) {
			String p_dflt   = parameter.getAttribute("default");
			ret = new TemplateParameter(
					TemplateParameterType.ParameterType_Int,
					name, p_dflt, null);
			
		} else if (type.equals("composite")) {
			String p_deftype = parameter.getAttribute("deftype");
			
			// Search for the defini
			TemplateParameterComposite deftype = findCompositeDef(t, p_deftype);
			
			TemplateParameterComposite p = deftype.clone();
			p.setName(name);
			
//			setCompositeItemNames(p);
			
			ret = p;
		} else if (type.equals("group")) {
			TemplateParameterGroup p = new TemplateParameterGroup(name);
			
			NodeList parameters_nl = parameter.getElementsByTagName("parameter");

			for (int i=0; i<parameters_nl.getLength(); i++) {
				Element parameter_e = (Element)parameters_nl.item(i);
				TemplateParameterBase gp = parseParameter(t, parameter_e);

				if (gp != null) {
					p.addParameter(gp);
				}
			}
			ret = p;
		} else {
			// ERROR:
			System.out.println("[ERROR] Unknown parameter type \"" + type + "\"");
		}
		
		if (ret != null) {
			ret.setDescription(description);
		}
		
		return ret;
	}
	
	private void setCompositeItemNames(TemplateParameterComposite p) {
		String pname = p.getName();
		
		for (TemplateParameterBase pc : p.getParameters()) {
			pc.setName(pname + "." + pc.getName());
			
			if (pc.getType() == TemplateParameterType.ParameterType_Composite) {
				setCompositeItemNames((TemplateParameterComposite)pc);
			}
		}
	}
	
	private TemplateParameterComposite findCompositeDef(TemplateInfo t, String deftype) {
		for (TemplateParameterComposite c : t.getCompositeTypes()) {
			if (c.getName().equals(deftype)) {
				return c;
			}
		}
		return null;
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

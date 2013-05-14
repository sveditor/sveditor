package net.sf.sveditor.svt.core.templates;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
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
		
		List<Element> sv_template_list = getElementsByTagName(fDocument, "sv_template");
		
		if (sv_template_list.size() == 0) {
			return;
		}
		
		Element sv_template = sv_template_list.get(0);
		
		List<Element> category_list = getElementsByTagName(sv_template, "category");
		for (int i=0; i<category_list.size(); i++) {
			addCategory(category_list.get(i));
		}
		
		List<Element> template_list = getElementsByTagName(sv_template, "template");
		for (int i=0; i<template_list.size(); i++) {
			addTemplate(template_list.get(i));
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
		
		List<Element> dl = getElementsByTagName(category, "description");
		
		if (dl.size() > 0) {
			Element desc = dl.get(0);
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
		
		
		Element description = getElementByTagName(template, "description");
		
		if (description != null) {
			t.setDescription(description.getTextContent());
		}
		
		// First, parse the composite template types
		Element compositeTypes = getElementByTagName(template, "compositeTypes");
		
		if (compositeTypes != null) {
			List<Element> compositeTypes_list = getElementsByTagName(compositeTypes, "compositeType");
			
			for (int i=0; i<compositeTypes_list.size(); i++) {
				Element compositeType = compositeTypes_list.get(i);
				TemplateParameterComposite composite = parseCompositeType(t, compositeType);
				t.addCompositeType(composite);
			}
		}
		
		Element files = getElementByTagName(template, "files");
		
		if (files != null) {
			List<Element> file_list = getElementsByTagName(files, "file");
			
			for (int i=0; i<file_list.size(); i++) {
				Element file = file_list.get(i);
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
		
		Element parameters = getElementByTagName(template, "parameters");
		
		if (parameters != null) {
			NodeList children = parameters.getChildNodes();
			
			for (int i=0; i<children.getLength(); i++) {
				Node n = children.item(i);
				if (n.getNodeName().equals("parameter")) {
					Element parameter = (Element)n;

					TemplateParameterBase p = parseParameter(t, parameter);

					if (p != null) {
						t.addParameter(p);
					}
				} else if (n.getNodeName().equals("group")) {
					Element group = (Element)n;

					TemplateParameterGroup g = parseGroup(t, group);

					if (g != null) {
						t.addParameter(g);
					}

				}
			}
		}
		
		fTemplates.add(t);
	}
	
	private TemplateParameterComposite parseCompositeType(TemplateInfo t, Element compositeType) {
		TemplateParameterComposite ret = null;
		String description 	= "";
		String name 		= null;
		
		Element description_nl = getElementByTagName(compositeType, "description");
		
		if (description_nl != null) {
			description = description_nl.getTextContent();
		}
		
		name = compositeType.getAttribute("name");
		
		ret = new TemplateParameterComposite();
		ret.setName(name);
		ret.setDescription(description);

		List<Element> parameters_nl = getElementsByTagName(compositeType, "parameter");
		
		for (int i=0; i<parameters_nl.size(); i++) {
			Element parameter_e = parameters_nl.get(i);
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
		
		Element desc_n = getElementByTagName(parameter, "description");
		String description = null;
		
		if (desc_n != null) {
			description = desc_n.getTextContent();
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
		}/** else if (type.equals("group")) {
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
		}*/ else {
			// ERROR:
			System.out.println("[ERROR] Unknown parameter type \"" + type + "\"");
		}
		
		if (ret != null) {
			ret.setDescription(description);
		}
		
		return ret;
	}
	
	private TemplateParameterGroup parseGroup(TemplateInfo t, Element group) {
		TemplateParameterGroup ret = null;
		
		String name = group.getAttribute("name");

		if (name != null) {
			ret = new TemplateParameterGroup(name);
			String description = null;
			
			if (group.hasAttribute("hidden")) {
				ret.setIsHidden(group.getAttribute("hidden").equals("true"));
			}

			NodeList nl = group.getChildNodes();
			
			for (int i=0; i<nl.getLength(); i++) {
				Node n = nl.item(i);
				
				if (n.getNodeName().equals("parameter")) {
					TemplateParameterBase p = parseParameter(t, (Element)n);
					ret.addParameter(p);
				} else if (n.getNodeName().equals("group")) {
					TemplateParameterGroup g = parseGroup(t, (Element)n);
					ret.addParameter(g);
				} else if (n.getNodeName().equals("description")) {
					description = n.getTextContent();
				}
			}
			
			if (description != null) {
				ret.setDescription(description);
			}
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

	private List<Element> getElementsByTagName(Node element, String tag) {
		List<Element> ret = new ArrayList<Element>();

		NodeList nl = element.getChildNodes();
		
		for (int i=0; i<nl.getLength(); i++) {
			if (nl.item(i) instanceof Element && nl.item(i).getNodeName().equals(tag)) {
				ret.add((Element)nl.item(i));
			}
		}
		
		return ret;
	}
	
	private Element getElementByTagName(Node element, String tag) {
		NodeList nl = element.getChildNodes();
		
		for (int i=0; i<nl.getLength(); i++) {
			if (nl.item(i) instanceof Element && nl.item(i).getNodeName().equals(tag)) {
				return (Element)nl.item(i);
			}
		}
		
		return null;
	}	
}

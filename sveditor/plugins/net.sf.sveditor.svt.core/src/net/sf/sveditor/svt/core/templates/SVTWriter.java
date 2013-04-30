package net.sf.sveditor.svt.core.templates;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.Properties;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import net.sf.sveditor.core.Tuple;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class SVTWriter {
	private DocumentBuilder					fDocumentBuilder;
	private Document						fDocument;
	private Element							fRootElem;
	
	public SVTWriter() {
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		try {
			fDocumentBuilder = f.newDocumentBuilder();		
		} catch (Exception e) {
			e.printStackTrace();
		}
		fDocumentBuilder.setErrorHandler(fErrorHandler);
		fDocument = fDocumentBuilder.newDocument();
		fRootElem = fDocument.createElement("sv_template");
		fDocument.appendChild(fRootElem);
	}
	
	public void toStream(OutputStream out) {
		SAXTransformerFactory tf = (SAXTransformerFactory)SAXTransformerFactory.newInstance();

		try {
			
			DOMSource ds = new DOMSource(fDocument);
			StreamResult sr = new StreamResult(out);
			tf.setAttribute("indent-number", new Integer(4));
			TransformerHandler th = tf.newTransformerHandler();
			
			Properties format = new Properties();
			format.put(OutputKeys.METHOD, "xml");
//			format.put("{http://xml. customer .org/xslt}indent-amount", "4");
//			format.put("indent-amount", "4");
//			format.put(OutputKeys.DOCTYPE_SYSTEM, "myfile.dtd");
			format.put(OutputKeys.ENCODING, "UTF-8");
			format.put(OutputKeys.INDENT, "yes");
			
			th.getTransformer().setOutputProperties(format);
			th.setResult(sr);
			th.getTransformer().transform(ds, sr);
		} catch (Exception e) {
			e.printStackTrace();
		}		
	}
	
	public String toString() {
		ByteArrayOutputStream out = new ByteArrayOutputStream();

		toStream(out);
		
		return out.toString();
	}
	
	public void writeCategory(TemplateCategory category) {
		
	}
	
	public void writeTemplateInfo(TemplateInfo template) {
		Element template_e = fDocument.createElement("template");
		setAttrIfNotNull(template_e, "name", template.getName());
		setAttrIfNotNull(template_e, "id", template.getId());
		setAttrIfNotNull(template_e, "category", template.getCategoryId());
		setAttrIfNotNull(template_e, "genscript", template.getGenerateScript());
		
		// description
		if (template.getDescription() != null &&
				!template.getDescription().trim().equals("")) {
			Element descElement = fDocument.createElement("description");
			descElement.setTextContent(template.getDescription());
			template_e.appendChild(descElement);
		}
	
		// compositeTypes
		Element compositeTypes = fDocument.createElement("compositeTypes");
		for (TemplateParameterComposite ct : template.getCompositeTypes()) {
			writeCompositeType(compositeTypes, ct);
		}
		template_e.appendChild(compositeTypes);
	
		// Files
		Element files = writeFiles(template);
		template_e.appendChild(files);
		
		// Parameters
		Element parameters_e = fDocument.createElement("parameters");
		for (TemplateParameterBase p : template.getParameters().getParameters()) {
			writeParameter(parameters_e, p);
		}
		template_e.appendChild(parameters_e);
		
		fRootElem.appendChild(template_e);
	}
	
	private void writeCompositeType(Element composite_types, TemplateParameterComposite ct) {
		Element composite_e = fDocument.createElement("composite");
		
		setAttrIfNotNull(composite_e, "name", ct.getName());
		
		if (ct.getDescription() != null && !ct.getDescription().trim().equals("")) {
			Element description = fDocument.createElement("description");
			description.setTextContent(ct.getDescription());
			composite_e.appendChild(description);
		}
		
		for (TemplateParameterBase p : ct.getParameters()) {
			writeParameter(composite_e, p);
		}
	}
	
	private Element writeFiles(TemplateInfo template) {
		Element files = fDocument.createElement("files");
		
		for (Tuple<String, String> file : template.getTemplates()) {
			Element file_e = fDocument.createElement("file");
			setAttrIfNotNull(file_e, "name", file.first());
			setAttrIfNotNull(file_e, "template", file.second());
			if (template.getExecutable(file.first())) {
				file_e.setAttribute("executable", "true");
			}
			files.appendChild(file_e);
		}
		
		return files;
	}
	
	private void writeParameter(Element parameters_e, TemplateParameterBase p) {
		Element parameter_e = fDocument.createElement("parameter");
		String type = null;
	
		setAttrIfNotNull(parameter_e, "name", p.getName());
		
		switch (p.getType()) {
			case ParameterType_Id: {
				type = "id";
				} break;
				
			case ParameterType_Int:
				type = "int";
				break;
				
			case ParameterType_Bool:
				type = "bool";
				break;
				
			case ParameterType_Class:
				type = "class";
				break;
				
			case ParameterType_Composite:
				type = "composite";
				break;
				
			case ParameterType_Enum:
				type = "enum";
				break;
				
			case ParameterType_Group:
				type = "group";
				break;
		}
		
		parameter_e.setAttribute("type", type);
		
		if (p.getDescription() != null && !p.getDescription().trim().equals("")) {
			Element description = fDocument.createElement("description");
			description.setTextContent(p.getDescription());
			parameter_e.appendChild(description);
		}
	
		if (p.getType() == TemplateParameterType.ParameterType_Bool ||
				p.getType() == TemplateParameterType.ParameterType_Enum ||
				p.getType() == TemplateParameterType.ParameterType_Id ||
				p.getType() == TemplateParameterType.ParameterType_Int) {
			// Basic parameter
			TemplateParameter pp = (TemplateParameter)p;
			setAttrIfNotNull(parameter_e, "default", pp.getDefault());
			
			if (pp.getValues().size() > 0) {
				StringBuilder restrictions = new StringBuilder();
				for (int i=0; i<pp.getValues().size(); i++) {
					restrictions.append(pp.getValues().get(i));
					if (i+1 < pp.getValues().size()) {
						restrictions.append(", ");
					}
				}
				parameter_e.setAttribute("restrictions", restrictions.toString());
			}
		} else if (p.getType() == TemplateParameterType.ParameterType_Composite) {
			TemplateParameterComposite pc = (TemplateParameterComposite)p;
			setAttrIfNotNull(parameter_e, "deftype", pc.getDefinitionType());
		} else if (p.getType() == TemplateParameterType.ParameterType_Group) {
			TemplateParameterGroup pg = (TemplateParameterGroup)p;
			
			for (TemplateParameterBase tp : pg.getParameters()) {
				writeParameter(parameter_e, tp);
			}
		}
		
		parameters_e.appendChild(parameter_e);
	}
	
	private static void setAttrIfNotNull(Element e, String attr, String val) {
		if (val != null && !val.trim().equals("")) {
			e.setAttribute(attr, val);
		}
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

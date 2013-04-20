package net.sf.sveditor.svt.core.templates;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class SVTUtils {
	
	public static boolean ensureExpectedSections(Document doc, Element sv_template) {
		NodeList nl = sv_template.getChildNodes();
		boolean ret = false;
		
		for (int i=0; i<nl.getLength(); i++) {
			Node n = nl.item(i);
			
			if (n instanceof Element) {
				Element e = (Element)n;
				if (e.getNodeName().equals("template")) {
					ret |= ensureExpectedTemplateSections(doc, e);
				} else if (e.getNodeName().equals("category")) {
					ret |= ensureExpectedCategorySections(doc, e);
				}
			}
			
		}
		
		return ret;
	}
	
	private static boolean ensureExpectedTemplateSections(Document doc, Element template) {
		boolean ret = false;
		
		ret |= addElementIfMissing(doc, template, "description");
		ret |= addElementIfMissing(doc, template, "parameters");
		ret |= addElementIfMissing(doc, template, "files");
		
		return ret;
	}

	private static boolean ensureExpectedCategorySections(Document doc, Element template) {
		boolean ret = false;
		
		ret |= addElementIfMissing(doc, template, "description");
		
		return ret;
	}

	private static boolean addElementIfMissing(Document doc, Element e, String elem) {
		NodeList nl = e.getChildNodes();
		boolean found = false;
		boolean ret = false;
		
		for (int i=0; i<nl.getLength(); i++) {
			Node n = nl.item(i);
			
			if (n instanceof Element && ((Element)n).getNodeName().equals(elem)) {
				found = true;
				break;
			}
		}
		
		if (!found) {
			Element new_e = doc.createElement(elem);
			e.appendChild(new_e);
			ret = true;
		}
		
		return ret;
	}

}

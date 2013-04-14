package net.sf.sveditor.svt.editor;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.w3c.dom.Element;

public class SVTLabelProvider extends LabelProvider {

	@Override
	public Image getImage(Object element) {
		// TODO Auto-generated method stub
		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof Element) {
			Element e = (Element)element;
			if (e.getNodeName().equals("template")) {
				return getAttr(e, "name", "[Unnamed]"); 
			} else if (e.getNodeName().equals("parameters")) {
				return "Parameters";
			} else if (e.getNodeName().equals("parameter")) {
				return getAttr(e, "name", "[Unnamed]") + " : " + getAttr(e, "type", "[Untyped]");
			} else if (e.getNodeName().equals("files")) {
				return "Files";
			} else if (e.getNodeName().equals("file")) {
				return getAttr(e, "name", "[Unnamed]") + " : " + getAttr(e, "template", "[Unspecified]");
			} else if (e.getNodeName().equals("category")) {
				return getAttr(e, "name", "[Unnamed]");
			} else {
				return super.getText(element);
			}
		} else if (element instanceof String) {
			return ((String)element);
		} else {
			return super.getText(element);
		}
	}

	private String getAttr(Element e, String attr, String dflt) {
		String ret = e.getAttribute(attr);
		
		if (ret == null) {
			ret = dflt;
		}
		
		return ret;
	}
	
}

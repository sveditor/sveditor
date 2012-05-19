package net.sf.sveditor.ui.svt.editor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class SVTContentProvider implements ITreeContentProvider {
	private Document			fDocument;
	private Element				fRoot;

	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fDocument = (Document)newInput;
		
		if (fDocument != null) {
			NodeList nl = fDocument.getElementsByTagName("sv_template");
			if (nl.getLength() > 0) {
				fRoot = (Element)nl.item(0);
			} else {
				fRoot = null;
			}
		}
	}

	public Object[] getElements(Object inputElement) {
		return new Object[] {"Templates", "Categories"};
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof String) {
			NodeList nl = fDocument.getElementsByTagName("sv_template");
			List<Node> ret = new ArrayList<Node>();
			String s = (String)parentElement;
			if (nl.getLength() > 0) {
				Element sv_template = (Element)nl.item(0);
				if (s.equals("Templates")) {
					if (sv_template != null) {
						nl = sv_template.getElementsByTagName("template");
					}
				} else if (s.equals("Categories")) {
					if (sv_template != null) {
						nl = sv_template.getElementsByTagName("category");
					}
				}
				for (int i=0; i<nl.getLength(); i++) {
					ret.add(nl.item(i));
				}
			}
			return ret.toArray();
		} else {
			Element e = (Element)parentElement;
			
			if (e.getNodeName().equals("sv_template")) {
				ArrayList<Element> ret = new ArrayList<Element>();
				NodeList nl = e.getChildNodes();
				
				for (int i=0; i<nl.getLength(); i++) {
					Node n = nl.item(i);
					
					if (n instanceof Element) {
						Element el = (Element)n;
						if (el.getNodeName().equals("template")) {
							ret.add(el);
						}
					}
				}
				
				return ret.toArray();
			} else if (e.getNodeName().equals("template")) {
				ArrayList<Element> ret = new ArrayList<Element>();
				NodeList nl = e.getChildNodes();
				
				for (int i=0; i<nl.getLength(); i++) {
					Node n = nl.item(i);
					
					if (n instanceof Element) {
						Element el = (Element)n;
						if (el.getNodeName().equals("parameters") ||
								el.getNodeName().equals("files")) {
							ret.add(el);
						}
					}
				}
				
				return ret.toArray();
			} else if (e.getNodeName().equals("parameters")) {
				ArrayList<Element> ret = new ArrayList<Element>();
				NodeList nl = e.getChildNodes();
				
				for (int i=0; i<nl.getLength(); i++) {
					Node n = nl.item(i);
					
					if (n instanceof Element) {
						Element el = (Element)n;
						if (el.getNodeName().equals("parameter")) {
							ret.add(el);
						}
					}
				}
				
				return ret.toArray();
			} else if (e.getNodeName().equals("files")) {
				ArrayList<Element> ret = new ArrayList<Element>();
				NodeList nl = e.getChildNodes();
				
				for (int i=0; i<nl.getLength(); i++) {
					Node n = nl.item(i);
					
					if (n instanceof Element) {
						Element el = (Element)n;
						if (el.getNodeName().equals("file")) {
							ret.add(el);
						}
					}
				}
				
				return ret.toArray();
			} else {
				return new Object[0];
			}
		}
	}

	public Object getParent(Object element) {
		Object ret = null;
		System.out.println("getParent: " + element);
		
		if (element instanceof String) {
			ret = fRoot;
		} else if (element != fRoot) {
			Element e = (Element)element;
			if (e.getNodeName().equals("template")) {
				ret = "Templates";
			} else if (e.getNodeName().equals("category")) {
				ret = "Categories";
			} else {
				ret = e.getParentNode();
			}
		}
		
		System.out.println("parent=" + ret);
		return ret;
	}

	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

}

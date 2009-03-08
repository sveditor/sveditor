package net.sf.sveditor.core;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import net.sf.sveditor.core.db.project.SVDBPath;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class SVProjectFileWrapper {
	private Document			fDocument;
	private List<SVDBPath>	    fIncludePaths = new ArrayList<SVDBPath>();
	private List<SVDBPath>	    fBuildPaths   = new ArrayList<SVDBPath>();
	
	public SVProjectFileWrapper() {
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		DocumentBuilder b = null;
		
		try {
			b = f.newDocumentBuilder();
		} catch (Exception e) {
			throw new RuntimeException(e.getMessage());
		}
		
		fDocument = b.newDocument();
		init();
	}
	
	public SVProjectFileWrapper(InputStream in) throws Exception {
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		DocumentBuilder b = f.newDocumentBuilder();
		
		b.setErrorHandler(fErrorHandler);
		
		fDocument = b.parse(in);
		init();
	}
	
	
	private boolean init() {
		NodeList svprojectList = fDocument.getElementsByTagName("svproject");
		Element svproject;
		boolean change = false;
		
		if (svprojectList.getLength() == 0) {
			svproject = fDocument.createElement("svproject");
			fDocument.appendChild(svproject);
		} else {
			svproject = (Element)svprojectList.item(0);
		}
		
		change |= init_paths(svproject, "includePaths", "includePath", fIncludePaths);
		change |= init_paths(svproject, "buildPaths", "buildPath", fBuildPaths);
		
		return change;
	}
	
	private boolean init_paths(
			Element svproject, 
			String containerName, 
			String elementName,
			List<SVDBPath>   element_list) {
		boolean change = false;
		
		// Look for includePaths element
		NodeList pathsList = svproject.getElementsByTagName(containerName);
		
		Element paths = null;
		if (pathsList.getLength() > 0) {
			paths = (Element)pathsList.item(0);
		} else {
			paths = fDocument.createElement(containerName);
			svproject.appendChild(paths);
			change = true;
		}
		
		NodeList includePathList = paths.getElementsByTagName(elementName);
		
		for (int i=0; i<includePathList.getLength(); i++) {
			Element includePath = (Element)includePathList.item(i);
			
			String isWSRelPath = includePath.getAttribute("isWSRelPath");
			
			if (isWSRelPath == null) {
				isWSRelPath = "false";
			}
			
			String path = includePath.getAttribute("path");
			
			if (path == null) {
				path = "";
			}
			
			element_list.add(
					new SVDBPath(path, (isWSRelPath == "true"), false));
		}
		
		return change;
	}
	
	private void marshall() {
	
		NodeList svprojectList = fDocument.getElementsByTagName("svproject");
		Element svproject;
		
		if (svprojectList.getLength() == 0) {
			svproject = fDocument.createElement("svproject");
			fDocument.appendChild(svproject);
		} else {
			svproject = (Element)svprojectList.item(0);
		}
		
		marshall_paths(svproject, "includePaths", "includePath", fIncludePaths);
		marshall_paths(svproject, "buildPaths", "buildPath", fBuildPaths);
		
	}
	
	private void marshall_paths(
			Element				svproject,
			String				containerName,
			String				elementName,
			List<SVDBPath>		element_list) {
		
		NodeList pathsList = svproject.getElementsByTagName(containerName);
		
		Element paths = null;
		if (pathsList.getLength() > 0) {
			paths = (Element)pathsList.item(0);
		} else {
			paths = fDocument.createElement(containerName);
			svproject.appendChild(paths);
		}
		
		NodeList includePathList = paths.getElementsByTagName(elementName);
		
		// Remove these elements
		for (int i=0; i<includePathList.getLength(); i++) {
			paths.removeChild((Element)includePathList.item(i));
		}
		
		for (SVDBPath ip : element_list) {
			Element path = fDocument.createElement(elementName);
			
			path.setAttribute("isWSRelPath", "" + ip.isWSRelPath());
			path.setAttribute("path", ip.getPath());
			
			paths.appendChild(path);
		}
	}
			
	
	public List<SVDBPath> getIncludePaths() {
		return fIncludePaths;
	}
	
	public List<SVDBPath> getBuildPaths() {
		return fBuildPaths;
	}
	
	public void toStream(OutputStream out) {
		SAXTransformerFactory tf = (SAXTransformerFactory)SAXTransformerFactory.newInstance();
		// Transformer t = null;
		
		// Copy the data back to the SAX structure
		try {
			marshall();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		try {
			
			DOMSource ds = new DOMSource(fDocument);
			StreamResult sr = new StreamResult(out);
			tf.setAttribute("indent-number", new Integer(2));
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
	
	public SVProjectFileWrapper duplicate() {
		SVProjectFileWrapper ret = new SVProjectFileWrapper();
		
		ret.fBuildPaths.clear();
		ret.fIncludePaths.clear();
		
		ret.fBuildPaths.addAll(fBuildPaths);
		ret.fIncludePaths.addAll(fIncludePaths);
		
		return ret;
	}
	
	public void init(SVProjectFileWrapper fw) {
		fBuildPaths.clear();
		fIncludePaths.clear();
		
		fBuildPaths.addAll(fw.fBuildPaths);
		fIncludePaths.addAll(fw.fIncludePaths);
	}
	
	public boolean equals(Object other) {
		if (other instanceof SVProjectFileWrapper) {
			SVProjectFileWrapper p = (SVProjectFileWrapper)other;
			if (p.fIncludePaths.size() != fIncludePaths.size()) {
				return false;
			}
			for (int i=0; i<fIncludePaths.size(); i++) {
				if (!p.fIncludePaths.get(i).getPath().equals(
						fIncludePaths.get(i).getPath())) {
					return false;
				}
				if (p.fIncludePaths.get(i).isWSRelPath() !=
					fIncludePaths.get(i).isWSRelPath()) {
					return false;
				}
			}
			
			if (p.fBuildPaths.size() != fBuildPaths.size()) {
				return false;
			}
			for (int i=0; i<fBuildPaths.size(); i++) {
				if (!p.fBuildPaths.get(i).getPath().equals(
						fBuildPaths.get(i).getPath())) {
					return false;
				}
				if (p.fBuildPaths.get(i).isWSRelPath() !=
					fBuildPaths.get(i).isWSRelPath()) {
					return false;
				}
			}
			return true;
		}
		return false;
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

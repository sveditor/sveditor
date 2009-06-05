package net.sf.sveditor.core.db.project;

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


import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class SVProjectFileWrapper {
	private Document					fDocument;
	private List<SVDBPath>	    		fIncludePaths;
	private List<SVDBPath>	    		fLibraryPaths;
	private List<SVDBPath>	    		fBuildPaths;
	private List<SVDBPath>				fPluginPaths;
	private List<SVDBSourceCollection>	fSourceCollections;
	
	public SVProjectFileWrapper() {
		
		fIncludePaths 		= new ArrayList<SVDBPath>();
		fLibraryPaths       = new ArrayList<SVDBPath>();
		fBuildPaths 		= new ArrayList<SVDBPath>();
		fPluginPaths 		= new ArrayList<SVDBPath>();
		fSourceCollections 	= new ArrayList<SVDBSourceCollection>();
		
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
		fIncludePaths 		= new ArrayList<SVDBPath>();
		fLibraryPaths       = new ArrayList<SVDBPath>();
		fBuildPaths 		= new ArrayList<SVDBPath>();
		fPluginPaths 		= new ArrayList<SVDBPath>();
		fSourceCollections 	= new ArrayList<SVDBSourceCollection>();
		
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
		change |= init_paths(svproject, "pluginPaths", "pluginPath", fPluginPaths);
		change |= init_paths(svproject, "libraryPaths", "libraryPath", fLibraryPaths);
		change |= init_source_collections(svproject, "sourceCollections", 
				"sourceCollection", fSourceCollections);
		
		return change;
	}
	
	private boolean init_paths(
			Element 			svproject, 
			String 				containerName, 
			String 				elementName,
			List<SVDBPath>   	element_list) {
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
			
			String path = includePath.getAttribute("path");
			
			if (path == null) {
				path = "";
			}
			
			element_list.add(new SVDBPath(path, false));
		}
		
		return change;
	}

	private boolean init_source_collections(
			Element 						svproject, 
			String 							containerName, 
			String 							elementName,
			List<SVDBSourceCollection>   	element_list) {
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
		
		NodeList sourceCollectionList = paths.getElementsByTagName(elementName);
		
		for (int i=0; i<sourceCollectionList.getLength(); i++) {
			Element sourceCollection = (Element)sourceCollectionList.item(i);
			
			String baseLocation = sourceCollection.getAttribute("baseLocation");
			
			if (baseLocation == null) {
				// invalid entry
				continue;
			}
			SVDBSourceCollection c = new SVDBSourceCollection(baseLocation);
			
			// Now, look at include and exclude elements
			NodeList includeList = sourceCollection.getElementsByTagName("include");
			for (int j=0; j<includeList.getLength(); j++) {
				Element inc = (Element)includeList.item(j);
				
				String expr = inc.getAttribute("expr");
				if (expr != null && !expr.equals("")) {
					c.getIncludes().add(expr);
				}
			}

			NodeList excludeList = sourceCollection.getElementsByTagName("exclude");
			for (int j=0; j<excludeList.getLength(); j++) {
				Element excl = (Element)excludeList.item(j);
				
				String expr = excl.getAttribute("expr");
				if (expr != null && !expr.equals("")) {
					c.getExcludes().add(expr);
				}
			}

			element_list.add(c);
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
		marshall_paths(svproject, "libraryPaths", "libraryPath", fLibraryPaths);
		marshall_paths(svproject, "pluginPaths", "pluginPath", fPluginPaths);
		marshall_source_collections(svproject, fSourceCollections);
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
			
			path.setAttribute("path", ip.getPath());
			
			paths.appendChild(path);
		}
	}

	private void marshall_source_collections(
			Element							svproject,
			List<SVDBSourceCollection>		source_collections) {
		
		NodeList collectionsList = svproject.getElementsByTagName("sourceCollections");
		
		Element paths = null;
		if (collectionsList.getLength() > 0) {
			paths = (Element)collectionsList.item(0);
		} else {
			paths = fDocument.createElement("sourceCollections");
			svproject.appendChild(paths);
		}
		
		NodeList sourceCollections = paths.getElementsByTagName("sourceCollection");
		
		// Remove these elements
		for (int i=0; i<sourceCollections.getLength(); i++) {
			paths.removeChild((Element)sourceCollections.item(i));
		}
		
		for (SVDBSourceCollection c : source_collections) {
			Element path = fDocument.createElement("sourceCollection");
			
			path.setAttribute("baseLocation", c.getBaseLocation());
			
			for (String inc : c.getIncludes()) {
				Element inc_e = fDocument.createElement("include");
				inc_e.setAttribute("expr", inc);
				path.appendChild(inc_e);
			}

			for (String excl : c.getExcludes()) {
				Element excl_e = fDocument.createElement("exclude");
				excl_e.setAttribute("expr", excl);
				path.appendChild(excl_e);
			}
			
			paths.appendChild(path);
		}
	}

	
	public List<SVDBPath> getIncludePaths() {
		return fIncludePaths;
	}
	
	public List<SVDBPath> getLibraryPaths() {
		return fLibraryPaths;
	}
	
	public List<SVDBPath> getBuildPaths() {
		return fBuildPaths;
	}
	
	public List<SVDBPath> getPluginPaths() {
		return fPluginPaths;
	}
	
	public List<SVDBSourceCollection> getSourceCollections() {
		return fSourceCollections;
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

		ret.init(this);
		
		return ret;
	}
	
	public void init(SVProjectFileWrapper fw) {
		fIncludePaths.clear();
		fPluginPaths.clear();
		fLibraryPaths.clear();
		fSourceCollections.clear();
		fBuildPaths.clear();
		
		for (SVDBPath p : fw.fIncludePaths) {
			fIncludePaths.add(p.duplicate());
		}
		
		for (SVDBPath p : fw.getLibraryPaths()) {
			fLibraryPaths.add(p.duplicate());
		}
		
		for (SVDBPath p : fw.getPluginPaths()) {
			fPluginPaths.add(p.duplicate());
		}
		
		for (SVDBSourceCollection c : fw.fSourceCollections) {
			fSourceCollections.add(c.duplicate());
		}
		
		for (SVDBPath p : fw.fBuildPaths) {
			fBuildPaths.add(p.duplicate());
		}
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
			}
			
			if (p.fLibraryPaths.size() != fLibraryPaths.size()) {
				return false;
			}
			
			for (int i=0; i<fLibraryPaths.size(); i++) {
				if (!p.fLibraryPaths.get(i).equals(fLibraryPaths.get(i))) {
					return false;
				}
			}

			if (fSourceCollections.size() != p.fSourceCollections.size()) {
				return false;
			}
			
			for (int i=0; i<fSourceCollections.size(); i++) {
				if (!p.fSourceCollections.get(i).equals(fSourceCollections.get(i))) {
					return false;
				}
			}
			
			if (fPluginPaths.size() != p.fPluginPaths.size()) {
				return false;
			}
			
			for (int i=0; i<fPluginPaths.size(); i++) {
				if (!p.fPluginPaths.get(i).equals(fPluginPaths.get(i))) {
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

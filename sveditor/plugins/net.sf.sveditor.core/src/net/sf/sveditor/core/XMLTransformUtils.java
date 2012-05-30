package net.sf.sveditor.core;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.CDATASection;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class XMLTransformUtils {
	
	public static Map<String, String> xml2Map(
			InputStream			content,
			String				root_elem_id,
			String				item_elem_id) throws Exception {
		Map<String, String> ret = new HashMap<String, String>();
		DocumentBuilder b = documentBuilder();
		
		Document doc = b.parse(content);
		
		NodeList root_list = doc.getElementsByTagName(root_elem_id);
		
		if (root_list.getLength() > 0) {
			Element root = (Element)root_list.item(0);
		
			NodeList item_list = root.getElementsByTagName(item_elem_id);
			for (int i=0; i<item_list.getLength(); i++) {
				Element item = (Element)item_list.item(i);
				String id = item.getAttribute("id");
				String value = item.getTextContent();
				ret.put(id, value);
			}
		}
		
		return ret;
	}
	
	public static String map2Xml(
			Map<String, String>	content,
			String				root_elem_id,
			String				item_elem_id) throws Exception {
		DocumentBuilder b = documentBuilder();
		Document doc = b.newDocument();
		String str = null;
		SAXTransformerFactory tf = (SAXTransformerFactory)SAXTransformerFactory.newInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		
		Element root = doc.createElement(root_elem_id);
		doc.appendChild(root);
		
		// Now, add all the children
		for (Entry<String, String> e : content.entrySet()) {
			Element item = doc.createElement(item_elem_id);
			item.setAttribute("id", e.getKey());
			CDATASection data = doc.createCDATASection(e.getValue());
			item.appendChild(data);
			root.appendChild(item);
		}
		
		try {
			DOMSource ds = new DOMSource(doc);
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
			
			str = out.toString();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return str;
	}

	private static DocumentBuilder documentBuilder() throws Exception {
		DocumentBuilder b = null;
		
		try {
			DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
			b = f.newDocumentBuilder();
			
			b.setErrorHandler(fErrorHandler);
		} catch (ParserConfigurationException e) {
			throw e;
		}
		
		return b;
	}
	
	private static ErrorHandler fErrorHandler = new ErrorHandler() {

		public void error(SAXParseException arg0) throws SAXException {
			throw arg0;
		}

		public void fatalError(SAXParseException arg0) throws SAXException {
			throw arg0;
		}

		public void warning(SAXParseException arg0) throws SAXException {}
	};
}

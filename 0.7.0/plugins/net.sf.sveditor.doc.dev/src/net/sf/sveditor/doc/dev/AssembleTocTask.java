/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.doc.dev;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.taskdefs.MatchingTask;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class AssembleTocTask extends MatchingTask {
	private String[]				fFiles;
	private String					fOutput = "toc.xml";
	private String					fLabel  = "";
	
	public void setOutput(String output) {
		fOutput = output;
	}
	
	public void setLabel(String label) {
		fLabel = label;
	}
	
	public void setFiles(String files) {
		fFiles = files.split(",");
		
		for (int i=0; i<fFiles.length; i++) {
			fFiles[i] = fFiles[i].trim();
		}
	}
	
	@Override
	public void execute() throws BuildException {
		System.out.println("AssembleTocTask: execute()");

		try {
			run();
		} catch (Exception e) {
			throw new BuildException(e);
		}
	}
	
	private void run() throws IOException, ParserConfigurationException, SAXException,
		TransformerConfigurationException, TransformerException {
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		Document doc_o = f.newDocumentBuilder().newDocument();
		FileOutputStream fos = new FileOutputStream(fOutput);
		
		Element toc = doc_o.createElement("toc");
		toc.setAttribute("label", fLabel);
		doc_o.appendChild(toc);
		
		for (String file : fFiles) {
			InputStream in = new FileInputStream(file);
			DocumentBuilder b = f.newDocumentBuilder();
			b.setErrorHandler(fErrorHandler);

			Document d = b.parse(in);
			Node toc_n = d.getFirstChild();
			NodeList nl = toc_n.getChildNodes(); // d.getElementsByTagName("topic");
			for (int i=0; i<nl.getLength(); i++) {
				Node n = nl.item(i);
				System.out.println("node: " + n.getNodeName());
				Node n_p = doc_o.importNode(n, true);
				toc.appendChild(n_p);
			}
		}
		
		SAXTransformerFactory tf = (SAXTransformerFactory)SAXTransformerFactory.newInstance();
		DOMSource ds = new DOMSource(doc_o);
		StreamResult sr = new StreamResult(fos);
		tf.setAttribute("indent-number", new Integer(2));
		TransformerHandler th = tf.newTransformerHandler();
		
		Properties format = new Properties();
		format.put(OutputKeys.METHOD, "xml");
		format.put(OutputKeys.ENCODING, "UTF-8");
		format.put(OutputKeys.INDENT, "yes");
		
		th.getTransformer().setOutputProperties(format);
		th.setResult(sr);
		th.getTransformer().transform(ds, sr);
		
		fos.close();
	}
	
	private ErrorHandler fErrorHandler = new ErrorHandler() {
		
		public void warning(SAXParseException arg0) throws SAXException {
			// TODO Auto-generated method stub
			
		}
		
		public void fatalError(SAXParseException arg0) throws SAXException {
			// TODO Auto-generated method stub
			
		}
		
		public void error(SAXParseException arg0) throws SAXException {
			// TODO Auto-generated method stub
			
		}
	};
	
	
	
	

}

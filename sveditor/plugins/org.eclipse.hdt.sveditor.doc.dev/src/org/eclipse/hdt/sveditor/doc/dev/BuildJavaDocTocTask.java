/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.doc.dev;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Properties;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.taskdefs.MatchingTask;
import org.apache.tools.ant.types.FileSet;
import org.apache.tools.ant.types.resources.FileResource;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class BuildJavaDocTocTask extends MatchingTask {
	private String						fOutput;		
	private String						fBase;
	private String						fLabel;
	private List<FileSet>				fFileSetList = new ArrayList<FileSet>();
	
	private class PackageFileRef {
		public File				fFile;
		public String			fPackage;
		
		public PackageFileRef(File file, String pkg) {
			fFile = file;
			fPackage = pkg;
		}
	}
	
	private List<PackageFileRef>		fPackageList = new ArrayList<PackageFileRef>();
	
	public void setLabel(String label) {
		fLabel = label;
	}
	
	public void setBase(String base) {
		fBase = base;
	}
	
	public void setOutput(String output) {
		fOutput = output;
	}
	
	public void addFileSet(FileSet fs) {
		fFileSetList.add(fs);	
	}

	@Override
	@SuppressWarnings({"unchecked","rawtypes"})
	public void execute() throws BuildException {
		for (FileSet fs : fFileSetList) {
			Iterator fs_i = fs.iterator();
			while (fs_i.hasNext()) {
				FileResource fr = (FileResource)fs_i.next();
				String pkg_name = getPackageName(fr.getFile());
				fPackageList.add(new PackageFileRef(fr.getFile(), pkg_name));
			}
		}
		
		for (int i=0; i<fPackageList.size(); i++) {
			for (int j=i+1; j<fPackageList.size(); j++) {
				PackageFileRef r_i = fPackageList.get(i);
				PackageFileRef r_j = fPackageList.get(j);
				
				if (r_i.fPackage.compareTo(r_j.fPackage) > 0) {
					fPackageList.set(i, r_j);
					fPackageList.set(j, r_i);
				}
			}
		}
		
		try {
			DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
			Document doc_o = f.newDocumentBuilder().newDocument();
			FileOutputStream fos = new FileOutputStream(fOutput);
			
			Element toc = doc_o.createElement("toc");
			toc.setAttribute("label", fLabel);
			doc_o.appendChild(toc);
			
			Element api_topic = doc_o.createElement("topic");
			api_topic.setAttribute("label", fLabel);
			toc.appendChild(api_topic);
			
			for (PackageFileRef r : fPackageList) {
				Element package_topic = doc_o.createElement("topic");
				package_topic.setAttribute("label", r.fPackage);
				package_topic.setAttribute("href", 
						r.fFile.getAbsolutePath().substring(fBase.length()));
				api_topic.appendChild(package_topic);
			}
			
			SAXTransformerFactory tf = (SAXTransformerFactory)SAXTransformerFactory.newInstance();
			DOMSource ds = new DOMSource(doc_o);
			StreamResult sr = new StreamResult(fos);
			TransformerHandler th = tf.newTransformerHandler();
			th.getTransformer().setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
			
			Properties format = new Properties();
			format.put(OutputKeys.METHOD, "xml");
			format.put(OutputKeys.ENCODING, "UTF-8");
			format.put(OutputKeys.INDENT, "yes");
			
			th.getTransformer().setOutputProperties(format);
			th.setResult(sr);
			th.getTransformer().transform(ds, sr);
			
			fos.close();
		} catch (Exception e) {
			throw new BuildException(e);
		}
	}
	
	private String getPackageName(File package_file) throws BuildException {
		String pkg = null;
		try {
			FileInputStream in = new FileInputStream(package_file);
			StringBuilder sb = new StringBuilder();
			int ch = '\n';
			do {
				sb.setLength(0);
				while ((ch = in.read()) != -1 && ch != '\n') {
					sb.append((char)ch);
				}
				
				if (sb.toString().startsWith("Package ")) {
					pkg = sb.toString().substring("Package ".length()).trim();
					break;
				}
			} while (ch != -1);
			
			in.close();
		} catch (Exception e) {
			throw new BuildException(e);
		}
		
		return pkg;
	}
	
	

}

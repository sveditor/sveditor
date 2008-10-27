package net.sf.sveditor.core;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import net.sf.sveditor.core.db.project.SVDBIncludePath;

import org.w3c.dom.Document;

public class SVProjectFileWrapper {
	private Document				fDocument;
	private List<SVDBIncludePath>	fIncludePaths = new ArrayList<SVDBIncludePath>();
	
	public SVProjectFileWrapper() {
		
		fIncludePaths.add(new SVDBIncludePath("c:/tools/ovm/ovm-1.1/src", false));
		
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		DocumentBuilder b = null;
		
		try {
			b = f.newDocumentBuilder();
		} catch (Exception e) {
			throw new RuntimeException(e.getMessage());
		}
		
		fDocument = b.newDocument();
	}
	
	public SVProjectFileWrapper(InputStream in) throws Exception {
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		DocumentBuilder b = f.newDocumentBuilder();
		
		fDocument = b.parse(in);

	}
	
	public List<SVDBIncludePath> getIncludePaths() {
		return fIncludePaths;
	}
	
	public void toStream(OutputStream out) {
		DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
		
	}
	
	

}

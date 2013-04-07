package net.sf.sveditor.ui.svt.editor;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.templates.SVTUtils;
import net.sf.sveditor.ui.EditorInputUtils;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.editor.FormEditor;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class SVTEditor extends FormEditor {
	
	private TemplatePage					fTemplatePage;
	private TextEditorPage					fTextEditorPage;
	private LogHandle						fLog;
	private Document						fDocument;
	private Element							fRootElement;
	private boolean							fIsDirty;
	
	public SVTEditor() {
		fLog = LogFactory.getLogHandle("SVTEditor");
	}
	
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		DocumentBuilder b = null;
		
		try {
			DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
			b = f.newDocumentBuilder();
			
			b.setErrorHandler(fErrorHandler);
			
			InputStream in = EditorInputUtils.openInputStream(input);
			fDocument = b.parse(in);
			
			in.close();
		} catch (ParserConfigurationException e) {
			
		} catch (IOException e) {
			e.printStackTrace();
		} catch (SAXException e) {
			e.printStackTrace();
		}
		
		if (fDocument == null) {
			// Create a new one
			fDocument = b.newDocument();
			fRootElement = fDocument.createElement("sv_template");
			fDocument.appendChild(fRootElement);
		} else if (fDocument.getElementsByTagName("sv_template").getLength() == 0) {
			// Empty document
			fRootElement = fDocument.createElement("sv_template");
			fDocument.appendChild(fRootElement);
		} else {
			// Have content already
			fRootElement = (Element)fDocument.getElementsByTagName("sv_template").item(0);
		}
		
		super.init(site, input);

		// Fixup the file structure and mark 'dirty' if changed 
		if (SVTUtils.ensureExpectedSections(fDocument, fRootElement)) {
			fIsDirty = true;
			editorDirtyStateChanged();
		}
		
		setPartName(input.getName());
	}
	
	@Override
	public boolean isDirty() {
		return (super.isDirty() || fIsDirty);
	}

	@Override
	protected void commitPages(boolean onSave) {
		// TODO Auto-generated method stub
		super.commitPages(onSave);
	}

	@Override
	protected void pageChange(int newPageIndex) {
		// TODO Auto-generated method stub
		super.pageChange(newPageIndex);
	}

	@Override
	protected void addPages() {
		fTemplatePage = new TemplatePage(this);
//TODO:		fTextEditorPage = new TextEditorPage();
		
		try {
			addPage(fTemplatePage);
//TODO:			addPage(fTextEditorPage);
		} catch (PartInitException e) {
			fLog.error("Failed to add pages", e);
		}
		
		fTemplatePage.setRoot(fDocument, fRootElement);
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		SAXTransformerFactory tf = (SAXTransformerFactory)SAXTransformerFactory.newInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		
		
		if (getActivePage() == 0) {
			fTemplatePage.doSave(monitor);
		} else if (getActivePage() == 1) {
			fTextEditorPage.doSave(monitor);
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
			
			EditorInputUtils.setContents(getEditorInput(),
					new ByteArrayInputStream(out.toByteArray()));
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		fIsDirty = false;
	}

	@Override
	public void doSaveAs() {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isSaveAsAllowed() {
		return true;
	}
	
	@SuppressWarnings("unused")
	private void dump() {
		SAXTransformerFactory tf = (SAXTransformerFactory)SAXTransformerFactory.newInstance();
		
		try {
			DOMSource ds = new DOMSource(fDocument);
			StreamResult sr = new StreamResult(System.out);
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

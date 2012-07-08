/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs.html;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Enumeration;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.DocTopicType;
import net.sf.sveditor.core.docs.IDocWriter;
import net.sf.sveditor.core.docs.model.DocFile;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.osgi.framework.Bundle;

public class HTMLDocWriter implements IDocWriter {
	
	private File indexHtmFile ;
	
	private class HTMLDocWriterException extends Exception {
		private static final long serialVersionUID = 567302255024887471L ;
		public HTMLDocWriterException(String msg) { super(msg) ; }
		@SuppressWarnings("unused")
		public HTMLDocWriterException(Exception e) { super(e) ; }
	}
	
	LogHandle log ;
	
	public HTMLDocWriter() {
		log = LogFactory.getLogHandle("HTMLDocWriter") ;
	}

	public void write(DocGenConfig cfg, DocModel model) {
		
		try {
			
			sanityCheck(cfg,model) ;
			
			log.debug(ILogLevel.LEVEL_MIN, "Generating documentation at: " + cfg.getOutputDir()) ;
			
			buildDirTree(cfg, model) ;
			
			writeFiles(cfg, model) ;
			
			writeIndices(cfg, model) ; 
			
		} catch (Exception e) {
			log.error("Exception detected while generated HTML documentation", e) ;
		} 

	}

	private void writeFiles(DocGenConfig cfg, DocModel model) throws IOException {
		for(String file: model.getFileSet()) {
			DocFile docFile = model.getDocFile(file) ;
			writeFile(cfg, model, docFile) ;
		}
	}

	private void writeFile(DocGenConfig cfg, DocModel model, DocFile docFile) {
		HTMLFileFactory fileFactory = new HTMLFileFactory(cfg) ;
		String srcPath = docFile.getDocPath() ;
		File outPath = HTMLUtils.getHTMLFileForSrcPath(cfg,srcPath) ;
		if(!outPath.getParentFile().exists()) outPath.getParentFile().mkdirs() ;
		log.debug(ILogLevel.LEVEL_MID, "Generating HTML file: " + outPath) ;
		FileOutputStream os;
		try {
			os = new FileOutputStream(outPath);
			String fileContent = fileFactory.build(docFile) ;
			if(fileContent == null || fileContent.isEmpty()) {
				log.error("Unpexpectedly generated no content for: " + docFile.getTitle()) ;
			}
			os.write(fileContent.getBytes()) ;
			os.close() ;
		} catch (Exception e) {
			log.error("Exception while opening for write: " + outPath, e) ;
		}
	}

	private void writeIndices(DocGenConfig cfg, DocModel model) throws IOException {
		for(DocTopicType docTopicType: model.getDocTopics().getAllTopicTypes()) {
			if(docTopicType.isIndex()) {
				writeIndex(cfg, model, docTopicType) ;
			}
		}
	}

	private void writeIndex(DocGenConfig cfg, DocModel model, DocTopicType docTopicType) throws IOException {
		
		HTMLIndexFactory classIndexFactory = new HTMLIndexFactory(cfg, docTopicType) ;
		File indexDir = new File(HTMLUtils.getHTMLDir(cfg),"index") ;
		
		File classIndexFile = new File(indexDir, "Classes.html") ;
		
		log.debug(ILogLevel.LEVEL_MID, "Generating class index to: " + classIndexFile) ;
		
		indexHtmFile = classIndexFile ; // FIXME: temp just to give the wizard something to open
		
		if(!classIndexFile.getParentFile().exists()) classIndexFile.getParentFile().mkdirs() ;
		
		FileOutputStream os ;
		os = new FileOutputStream(classIndexFile) ;
		os.write(classIndexFactory.build(model).getBytes()) ;
		os.close() ;
		
	}

	private void sanityCheck(DocGenConfig cfg, DocModel model) throws HTMLDocWriterException {
		
		if(cfg == null)
			throw new HTMLDocWriterException("Received null config") ;
		if(model == null)
			throw new HTMLDocWriterException("Received null model")  ;
		
		File outputDir = cfg.getOutputDir() ;
		
		if(outputDir.toString().isEmpty()) 
			throw new HTMLDocWriterException("Received empty output dir") ; 
		
	}

	private void buildDirTree(DocGenConfig cfg, DocModel model) throws Exception {
		
		log.debug(ILogLevel.LEVEL_MIN, "Building dir tree") ;
		
		copyBundleDirToFS("html", cfg.getOutputDir()) ;

	}
	
	
	public void copyBundleDirToFS(String srcBundlePath, File dstFSPathRoot) throws HTMLDocWriterException {
		
		Bundle bundle = SVCorePlugin.getDefault().getBundle() ;
		byte buffer[] = new byte[1024*1024] ;
		
		Enumeration<URL> entries = bundle.findEntries(srcBundlePath, "*", true) ;
		
		log.debug(ILogLevel.LEVEL_MID, "Copying bundle dir: " + srcBundlePath) ;
		
		while (entries.hasMoreElements()) {
			URL url = (URL)entries.nextElement() ;
			if (url.getPath().endsWith("/")) { continue ; }
			String fileSubPath = url.getPath() ;
			File target = new File(dstFSPathRoot, fileSubPath) ;
			
			log.debug(ILogLevel.LEVEL_MID, "Copying bundle path: " + fileSubPath) ;
		
			if (!target.getParentFile().exists()) {
				if (!target.getParentFile().mkdirs()) {
					throw new HTMLDocWriterException("Failed to create directory \"" + target.getParent() + "\"");
				}
			}
			try {
				FileOutputStream out = new FileOutputStream(target);
				InputStream in = url.openStream();
				int len;

				do {
					len = in.read(buffer, 0, buffer.length) ;
					if (len > 0) {
						out.write(buffer, 0, len) ;
					}
				} while (len > 0);
				
				out.close();
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
				throw new RuntimeException("Failed to copy file " + target);
			}
		}		
		
	}

	public File getIndexHTML(DocGenConfig cfg, DocModel model) {
		return indexHtmFile ;
	}
}

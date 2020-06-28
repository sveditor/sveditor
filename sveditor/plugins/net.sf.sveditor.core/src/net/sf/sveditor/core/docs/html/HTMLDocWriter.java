/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
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
	
	LogHandle fLog ;
	
	public HTMLDocWriter() {
		fLog = LogFactory.getLogHandle("HTMLDocWriter") ;
	}

	public void write(DocGenConfig cfg, DocModel model) {
		
		try {
			
			sanityCheck(cfg,model) ;
			
			fLog.debug(ILogLevel.LEVEL_MIN, "Generating documentation at: " + cfg.getOutputDir()) ;
			
			buildDirTree(cfg, model) ;
			
			assignOutPaths(cfg, model) ;
			
			writeFiles(cfg, model) ;
			
			writeIndices(cfg, model) ; 
			
		} catch (Exception e) {
			fLog.error("Exception detected while generated HTML documentation", e) ;
		} 

	}

	private void assignOutPaths(DocGenConfig cfg, DocModel model) {
		for(String file: model.getFileSet()) {
			DocFile docFile = model.getDocFile(file) ;
			String srcPath = docFile.getDocPath() ;
			File outPath = HTMLUtils.getHTMLFileForSrcPath(cfg,srcPath) ;
			docFile.setOutPath(outPath.toString()) ;
		}
	}

	private void writeFiles(DocGenConfig cfg, DocModel model) throws IOException {
		for(String file: model.getFileSet()) {
			DocFile docFile = model.getDocFile(file) ;
			writeFile(cfg, model, docFile) ;
		}
	}

	private void writeFile(DocGenConfig cfg, DocModel model, DocFile docFile) {
		HTMLFileFactory fileFactory = new HTMLFileFactory(cfg, model) ;
		File outPath = new File(docFile.getOutPath()) ;
		if(!outPath.getParentFile().exists()) outPath.getParentFile().mkdirs() ;
		fLog.debug(ILogLevel.LEVEL_MID, "Generating HTML file: " + outPath) ;
		FileOutputStream os;
		try {
			os = new FileOutputStream(outPath);
			String fileContent = fileFactory.build(docFile) ;
			if(fileContent == null || fileContent.isEmpty()) {
				fLog.error("Unpexpectedly generated no content for: " + docFile.getTitle()) ;
			}
			os.write(fileContent.getBytes()) ;
			os.close() ;
		} catch (Exception e) {
			fLog.error("Exception while opening for write: " + outPath, e) ;
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
		
		HTMLIndexFactory indexFactory = new HTMLIndexFactory(cfg, docTopicType) ;
		
		String topicName = docTopicType.getName() ;
		
		File indexFile = HTMLUtils.getHTMLFileForIndexOfTopic(cfg, docTopicType.getPluralName()) ;
		
		fLog.debug(ILogLevel.LEVEL_MIN, 
				String.format("Preparing index for topic(%s) at file(%s)", 
						topicName,
						indexFile.toString())) ;
		
		indexHtmFile = indexFile ; 
		
		if(!indexFile.getParentFile().exists()) indexFile.getParentFile().mkdirs() ;
		
		FileOutputStream os ;
		os = new FileOutputStream(indexFile) ;
		os.write(indexFactory.build(model).getBytes()) ;
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
		
		fLog.debug(ILogLevel.LEVEL_MIN, "Building dir tree") ;
		
		copyBundleDirToFS("html", cfg.getOutputDir()) ;

	}
	
	
	public void copyBundleDirToFS(String srcBundlePath, File dstFSPathRoot) throws HTMLDocWriterException {
		
		Bundle bundle = SVCorePlugin.getDefault().getBundle() ;
		byte buffer[] = new byte[1024*1024] ;
		
		Enumeration<URL> entries = bundle.findEntries(srcBundlePath, "*", true) ;
		
		fLog.debug(ILogLevel.LEVEL_MID, "Copying bundle dir: " + srcBundlePath) ;
		
		while (entries.hasMoreElements()) {
			URL url = (URL)entries.nextElement() ;
			if (url.getPath().endsWith("/")) { continue ; }
			String fileSubPath = url.getPath() ;
			File target = new File(dstFSPathRoot, fileSubPath) ;
			
			fLog.debug(ILogLevel.LEVEL_MID, "Copying bundle path: " + fileSubPath) ;
		
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

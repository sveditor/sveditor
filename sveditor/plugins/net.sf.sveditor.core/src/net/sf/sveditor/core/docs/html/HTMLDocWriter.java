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
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.DocModel;
import net.sf.sveditor.core.docs.IDocWriter;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.osgi.framework.Bundle;

public class HTMLDocWriter implements IDocWriter {
	
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
			
			writeClasses(cfg, model) ;
			writeIndices(cfg, model) ; 
			
		} catch (Exception e) {
			log.error("Exception detected while generated HTML documentation", e) ;
		} 

	}

	private void writeIndices(DocGenConfig cfg, DocModel model) throws IOException {
		writeClassIndex(cfg, model) ;
		
	}

	private void writeClassIndex(DocGenConfig cfg, DocModel model) throws IOException {
		
		HTMLClassIndexFactory classIndexFactory = new HTMLClassIndexFactory(cfg) ;
		File indexDir = new File(HTMLUtils.getHTMLDir(cfg),"index") ;
		
		File classIndexFile = new File(indexDir, "Classes.html") ;
		
		log.debug(ILogLevel.LEVEL_MID, "Generating class index to: " + classIndexFile) ;
		
		if(!classIndexFile.getParentFile().exists()) classIndexFile.getParentFile().mkdirs() ;
		
		FileOutputStream os ;
		os = new FileOutputStream(classIndexFile) ;
		os.write(classIndexFactory.build(model).getBytes()) ;
		os.close() ;
		
	}

	private void writeClasses(DocGenConfig cfg, DocModel model) throws IOException {
		HTMLClassFactory classFactory = new HTMLClassFactory(cfg) ;
		
		for(String pkgName: model.getClassMapByPkg().keySet()) {
			log.debug(ILogLevel.LEVEL_MID, "Generating class docs for pkg: " + pkgName) ;
			Map<String, SVDBDeclCacheItem> pkgClassMap = model.getClassMapByPkg().get(pkgName) ;
			for(String className: pkgClassMap.keySet()) {
				log.debug(ILogLevel.LEVEL_MID, "Generating class docs for class: " + pkgName + "::" + className) ;
				File outPath = HTMLUtils.getHTMLFileForClass(cfg,pkgName,className) ;
				SVDBDeclCacheItem classDecl = pkgClassMap.get(className) ;
				if(!outPath.getParentFile().exists()) outPath.getParentFile().mkdirs() ;
				log.debug(ILogLevel.LEVEL_MID, "HTML file: " + outPath) ;
				FileOutputStream os;
				os = new FileOutputStream(outPath);
				os.write(classFactory.build(classDecl).getBytes()) ;
				os.close() ;
			}
		}
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
}

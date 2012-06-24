/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs.model;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;


public class DocModelFactoryNew {
	
	private class DocModelFactoryException extends Exception {
		private static final long serialVersionUID = -6656720421849741060L;
		public DocModelFactoryException(String msg) {
			super(msg) ;
		}
	}
	
	private LogHandle fLog ;
	
	public DocModelFactoryNew() {
		fLog = LogFactory.getLogHandle("DocModelFactory") ;
	}

	public DocModelNew build(DocGenConfig cfg) {
		DocModelNew model = new DocModelNew() ;
		try {
			gatherPackages(cfg, model) ;
		} catch (DocModelFactoryException e) {
			fLog.error("Document model build failed: " + e.toString()) ;
		}
		return model ;
	}

	private void gatherPackages(DocGenConfig cfg, DocModelNew model) throws DocModelFactoryException {
		for(SVDBDeclCacheItem pkg: cfg.getSelectedPackages()) {
			DocPkgItem docPkgItem = createPkgItem(pkg) ; // FIXME: check for user defined docs
			if(docPkgItem != null) {
				model.getPkgMap().put(docPkgItem.getName(), docPkgItem) ;
			}
			Map<String, Map<String, DocClassItem>> classMapByPkg = model.getClassMapByPkg() ;
			classMapByPkg.put(pkg.getName(), new HashMap<String, DocClassItem>()) ;
			if(pkg.getParent() == null) {
				throw new DocModelFactoryException("Package had no parent index: " + pkg.getName()) ;
			}
			Map<String, DocClassItem> pkgClassMap = classMapByPkg.get(pkg.getName()) ;
			List<SVDBDeclCacheItem> pkgDecls = pkg.getParent().findPackageDecl(new NullProgressMonitor(), pkg) ; 
			if(pkgDecls != null) {
				for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
					if(pkgDecl.getType() == SVDBItemType.ClassDecl) {
						// FIXME: check for user defined class docs
						DocClassItem classDocItem = new DocClassItem(pkgDecl.getName()) ;
						docPkgItem.addChild(classDocItem) ;
						pkgClassMap.put(classDocItem.getName(), classDocItem) ;
						indexClass(docPkgItem, classDocItem, model) ;
					}
				}
			} else {
				fLog.debug("Package declarations for \"" + pkg.getName() + "\" not found");
			}			
		}
		
	}

	private DocPkgItem createPkgItem(SVDBDeclCacheItem pkg) {
		DocPkgItem item = new DocPkgItem(pkg.getName()) ;
		return item ;
	}

	private void indexClass(DocPkgItem pkgItem, DocClassItem classItem, DocModelNew model) throws DocModelFactoryException {
		String name = classItem.getName() ;
		String firstChar = name.substring(0, 1).toUpperCase() ;
		if(model.getClassIndexMap().containsKey(firstChar)) {
			model.getClassIndexMap().get(firstChar)
				.put(name, new Tuple<DocPkgItem, DocClassItem>(pkgItem,classItem)) ;
		} else if(firstChar.matches("[0123456789]")) {
			model.getClassIndexMap().get(DocModelNew.IndexKeyNum)
				.put(name,  new Tuple<DocPkgItem, DocClassItem>(pkgItem,classItem)) ;
		} else {
			model.getClassIndexMap().get(DocModelNew.IndexKeyWierd)
				.put(name,  new Tuple<DocPkgItem, DocClassItem>(pkgItem,classItem)) ;
		}
		
	}

}

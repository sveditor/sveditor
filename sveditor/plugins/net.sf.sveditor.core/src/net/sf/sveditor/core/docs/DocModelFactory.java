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

package net.sf.sveditor.core.docs;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;


public class DocModelFactory {
	
	private class DocModelFactoryException extends Exception {
		private static final long serialVersionUID = -6656720421849741060L;
		public DocModelFactoryException(String msg) {
			super(msg) ;
		}
	}
	
	private LogHandle log ;
	
	public DocModelFactory() {
		log = LogFactory.getLogHandle("DocModelFactory") ;
	}

	public DocModel build(DocGenConfig cfg) {
		DocModel model = new DocModel() ;
		try {
			gatherPackages(cfg, model) ;
			gatherClasses(cfg, model) ;
		} catch (DocModelFactoryException e) {
			log.error("Document model build failed: " + e.toString()) ;
		}
		return model ;
	}

	private void gatherPackages(DocGenConfig cfg, DocModel model) throws DocModelFactoryException {
		for(SVDBDeclCacheItem pkg: cfg.getSelectedPackages()) {
			model.getPkgMap().put(pkg.getName(), pkg) ;
			Map<String, Map<String, SVDBDeclCacheItem>> classMapByPkg = model.getClassMapByPkg() ;
			classMapByPkg.put(pkg.getName(), new HashMap<String, SVDBDeclCacheItem>()) ;
		}
		
	}

	private void gatherClasses(DocGenConfig cfg, DocModel model) throws DocModelFactoryException {
		for(String pkgName: model.getPkgMap().keySet()) {
			SVDBDeclCacheItem pkg = model.getPkgMap().get(pkgName) ;
			Map<String, Map<String, SVDBDeclCacheItem>> classMapByPkg = model.getClassMapByPkg() ;
			Map<String, SVDBDeclCacheItem> pkgClassMap = classMapByPkg.get(pkg.getName()) ;
			// Find all classes in the package
			if(pkg.getParent() == null)
				throw new DocModelFactoryException("pkg has no parent cache: " + pkg.getName()) ;
			List<SVDBDeclCacheItem> pkgDecls = pkg.getParent().findPackageDecl(new NullProgressMonitor(), pkg) ;
			for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
				if(pkgDecl.getType() == SVDBItemType.ClassDecl) {
					// TODO: filter out any classes filter by cfg
					pkgClassMap.put(pkgDecl.getName(), pkgDecl) ;
					indexClass(pkg,pkgDecl,model) ;
				}
			}
		}
		
	}
	
	private void indexClass(SVDBDeclCacheItem pkg, SVDBDeclCacheItem pkgDecl, DocModel model) throws DocModelFactoryException {
		if(!(pkgDecl.getSVDBItem() instanceof SVDBClassDecl))
			throw new DocModelFactoryException("Asked to index a decl item that is not a class") ;
		SVDBClassDecl classDecl = (SVDBClassDecl)pkgDecl.getSVDBItem() ;
		String name = classDecl.getName() ;
		String firstChar = name.substring(0, 1).toUpperCase() ;
		if(model.getClassIndexMap().containsKey(firstChar)) {
			model.getClassIndexMap().get(firstChar)
				.put(name, new Tuple<SVDBDeclCacheItem, SVDBDeclCacheItem>(pkg,pkgDecl)) ;
		} else if(firstChar.matches("[0123456789]")) {
			model.getClassIndexMap().get(DocModel.IndexKeyNum)
				.put(name,  new Tuple<SVDBDeclCacheItem, SVDBDeclCacheItem>(pkg,pkgDecl)) ;
		} else {
			model.getClassIndexMap().get(DocModel.IndexKeyWierd)
				.put(name,  new Tuple<SVDBDeclCacheItem, SVDBDeclCacheItem>(pkg,pkgDecl)) ;
		}
		
	}

}

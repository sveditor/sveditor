/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;

import org.eclipse.core.runtime.IProgressMonitor;



public interface ISVDBDeclCache extends ISVDBDeclCacheFileAttr {
	

	
	/**
	 * Returns a list of declarations from the global scope (class, module, interface, program, package, function, task)  
	 * @return
	 */
	List<SVDBDeclCacheItem> findGlobalScopeDecl(IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher);
	
	/**
	 * Returns an iterator over the files managed by this cache
	 * 
	 * @param monitor
	 * @return
	 */
	Iterable<String> getFileList(IProgressMonitor monitor);
	
	/**
	 * Returns an iterator over files with the specified attributes
	 */
	Iterable<String> getFileList(IProgressMonitor monitor, int flags);

	/**
	 * Finds the AST for the specified path
	 * 
	 * @param monitor
	 * @param filename
	 * @return
	 */
	SVDBFile findFile(IProgressMonitor monitor, String filename);

	/**
	 * Finds the pre-processor AST for the specified path
	 * 
	 * @param monitor
	 * @param filename
	 * @return
	 */
	SVDBFile findPreProcFile(IProgressMonitor monitor, String filename);

	/**
	 * Returns a list of declarations from within the specified package scope
	 * 
	 * @param pkg_item
	 * @return
	 */
	List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor, SVDBDeclCacheItem pkg_item);
	
	/**
	 * Returns the file in which the specified declaration-cache item is defined
	 * 
	 * @param item
	 * @return
	 */
	SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item);
	
	/**
	 * Returns the pre-processor version of the file in which the specified 
	 * declaration-cache item is defined
	 * 
	 * @param item
	 * @return
	 */
	SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item);
	
}

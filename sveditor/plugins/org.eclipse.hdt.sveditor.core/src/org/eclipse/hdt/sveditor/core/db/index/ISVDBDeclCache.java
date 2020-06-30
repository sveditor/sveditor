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
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.index;

import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.search.ISVDBFindNameMatcher;



public interface ISVDBDeclCache {
	
	int							FILE_ATTR_HAS_MARKERS	= (1 << 0);
	// 
	int							FILE_ATTR_SRC_FILE		= (1 << 1);
	int							FILE_ATTR_ARG_FILE		= (1 << 2);
	// Passing ROOT_FILE causes only root files to be returned
	int							FILE_ATTR_ROOT_FILE		= (1 << 3);
	int							FILE_ATTR_LIB_FILE		= (1 << 4);
	
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

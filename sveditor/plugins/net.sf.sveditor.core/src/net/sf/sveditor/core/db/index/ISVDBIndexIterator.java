/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
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

import org.eclipse.core.runtime.IProgressMonitor;


public interface ISVDBIndexIterator extends ISVDBDeclCache, ISVDBIndexOperationRunner, ISVDBIndexFileStructProvider {

	/**
	 * This method is deprecated. The 'findGlobal' methods should be
	 * used instead
	 * 
	 * @param monitor
	 * @return
	 */
	@Deprecated
	ISVDBItemIterator 		getItemIterator(IProgressMonitor monitor);

	int FIND_INC_SV_FILES      = 0x01;
	int FIND_INC_ARG_FILES     = 0x02;
	int FIND_INC_ALL_FILES     = 0x04;

	/**
	 * findIncludeFiles()
	 * 
	 * Locates include paths 
	 */
	List<SVDBIncFileInfo> findIncludeFiles(String root, int flags);
}

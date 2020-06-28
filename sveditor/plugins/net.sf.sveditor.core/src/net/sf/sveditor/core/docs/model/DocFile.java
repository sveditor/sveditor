/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

package net.sf.sveditor.core.docs.model;

import java.io.File;

public class DocFile extends DocTopic {
	
	String fDocPath ;
	String fPageTitle ;
	String fOutPath ;
	boolean fHasUsedSymbol ;  

	public DocFile(String name) {
		super(name, "", "") ;
		setDocFile(this) ;
		fHasUsedSymbol = false ;
	}
	
	public void markAsUsed() {
		fHasUsedSymbol = true ;
	}
	
	public void setOutPath(String path) {
		fOutPath = path ;
	}
	
	public String getOutPath() {
		return fOutPath ;
	}
	
	/**
	 * @return File name alone without any containing directories
	 */
	public String getSrcFileName() {
		File file = new File(fDocPath) ;
		return file.getName() ;
	}

	public void setDocPath(String path) {
		fDocPath = path ;
	}
	
	public String getDocPath() {
		return fDocPath ;
	}

	public String getPageTitle() {
		return fPageTitle ;
	}
	
	public void setPageTitle(String pageTitle) {
		fPageTitle = pageTitle ;
	}

}

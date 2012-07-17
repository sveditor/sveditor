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

import java.io.File;

public class DocFile extends DocTopic {
	
	String fDocPath ;
	String fPageTitle ;
	String fOutPath ;

	public DocFile(String name) {
		super(name, "", "") ;
		setDocFile(this) ;
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

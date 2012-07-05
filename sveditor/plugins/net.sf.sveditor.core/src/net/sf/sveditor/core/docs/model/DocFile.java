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

public class DocFile extends DocItem {
	
	String fDocPath ;

	public DocFile(String name) {
		super(name, DocItemType.FILE) ;
		setDocFile(this) ;
	}

	public void setDocPath(String path) {
		fDocPath = path ;
	}
	
	public String getDocPath() {
		return fDocPath ;
	}

}

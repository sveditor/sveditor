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

package net.sf.sveditor.core.db;

public class SVDBDocComment extends SVDBItem {
	
	public String fRawComment ;

	public SVDBDocComment() {
		super("", SVDBItemType.DocComment) ;
	}
	public SVDBDocComment(String title, String comment) {
		super(title, SVDBItemType.DocComment) ;
		fRawComment = comment ;
	}
	
	public String getRawComment() {
		return fRawComment ;
	}

}

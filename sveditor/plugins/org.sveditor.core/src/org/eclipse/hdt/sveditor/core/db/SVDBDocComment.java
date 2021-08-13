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

package org.sveditor.core.db;

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

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
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.expr_utils;

public class SVExprItemInfo {
	private SVExprItemType		fType;
	private String				fName;
	
	public SVExprItemInfo(
			SVExprItemType		type,
			String 				name) {
		fType = type;
		fName = name;
	}
	
	public SVExprItemType getType() {
		return fType;
	}
	
	public String getName() {
		return fName;
	}

}

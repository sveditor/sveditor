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


package org.eclipse.hdt.sveditor.core.db.stmt;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBTimePrecisionStmt extends SVDBStmt {
	public String				fArg1;				
	
	public SVDBTimePrecisionStmt() {
		super(SVDBItemType.TimePrecisionStmt);
	}
	
	public String getArg1() {
		return fArg1;
	}
	
	public void setArg1(String arg1) {
		fArg1 = arg1;
	}
}

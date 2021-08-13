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


package org.eclipse.hdt.sveditor.core.indent;

import java.util.List;

public class SVIndentStmt {
	protected List<SVIndentStmt>			fStmtList;
	protected SVIndentStmtType				fType;
	
	public SVIndentStmt(SVIndentStmtType type) {
		fType = type;
	}
	
	public SVIndentStmtType getType() {
		return fType;
	}

}

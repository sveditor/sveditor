/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFinalStmt extends SVDBBodyStmt {
	
	public SVDBFinalStmt() {
		super(SVDBItemType.FinalStmt);
	}

	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_final_stmt(this);
	}
}

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
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_time_precision_stmt(this);
	}
}

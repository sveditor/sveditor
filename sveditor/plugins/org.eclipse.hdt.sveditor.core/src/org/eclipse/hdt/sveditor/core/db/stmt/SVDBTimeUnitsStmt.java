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

public class SVDBTimeUnitsStmt extends SVDBStmt {
	public String				fUnits;
	public String				fPrecision;
	
	public SVDBTimeUnitsStmt() {
		super(SVDBItemType.TimeUnitsStmt);
	}
	
	public String getUnits() {
		return fUnits;
	}
	
	public void setUnits(String units) {
		fUnits = units;
	}

	public String getPrecision() {
		return fPrecision;
	}
	
	public void setPrecision(String Precision) {
		fPrecision = Precision;
	}
	
}

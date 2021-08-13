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

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBForStmt extends SVDBBodyStmt {
	public SVDBStmt			fInitExpr;
	public SVDBStmt			fTestStmt;
	public SVDBStmt			fIncrStmt;
	
	public SVDBForStmt() {
		super(SVDBItemType.ForStmt);
	}
	
	public SVDBStmt getInitExpr() {
		return fInitExpr;
	}
	
	public void setInitStmt(SVDBStmt stmt) {
		fInitExpr = stmt;
	}
	
	public SVDBStmt getTestExpr() {
		return fTestStmt;
	}
	
	public void setTestStmt(SVDBStmt stmt) {
		fTestStmt = stmt;
	}
	
	public SVDBStmt getIncrStmt() {
		return fIncrStmt;
	}
	
	public void setIncrstmt(SVDBStmt stmt) {
		fIncrStmt = stmt;
	}
	
	public SVDBForStmt duplicate() {
		return (SVDBForStmt)super.duplicate();
	}
	
	public void init(ISVDBItemBase other) {
		super.init(other);
		
		SVDBForStmt o = (SVDBForStmt)other;
		if (o.fIncrStmt != null) {
			fIncrStmt = o.fIncrStmt.duplicate();
		} else {
			fIncrStmt = null;
		}
		
		if (o.fTestStmt != null) {
			fTestStmt = o.fTestStmt.duplicate();
		} else {
			fTestStmt = null;
		}

		if (o.fInitExpr != null) {
			fInitExpr = o.fInitExpr.duplicate();
		} else {
			fInitExpr = null;
		}
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		
		if (!super.equals(obj, full)) {
			return false;
		}
		
		if (!(obj instanceof SVDBForStmt)) {
			return false;
		}
		
		SVDBForStmt o = (SVDBForStmt)obj;
		boolean ret = true;
		
		if (full) {
			if (fInitExpr == null || o.fInitExpr == null) {
				ret &= (fInitExpr == o.fInitExpr);
			} else {
				ret &= fInitExpr.equals(o.fInitExpr);
			}
			
			if (fTestStmt == null || o.getTestExpr() == null) {
				ret &= (fTestStmt == o.getTestExpr());
			} else {
				ret &= fTestStmt.equals(o.getTestExpr());
			}
			
			if (fIncrStmt == null || o.getIncrStmt() == null) {
				ret &= (fIncrStmt == o.getIncrStmt());
			} else {
				ret &= fIncrStmt.equals(o.getIncrStmt());
			}
		} 
		
		return ret;
	}
	
}

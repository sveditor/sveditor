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


package org.sveditor.core.db.stmt;

import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBTypeInfo;
import org.sveditor.core.db.expr.SVDBExpr;

/**
 * Holds type information about an array field or typedef
 * 
 * @author ballance
 *
 */
public class SVDBVarDimItem extends SVDBStmt {
	
	public enum DimType {
		Unsized,
		Sized,
		Associative,
		Queue
	};
	
	public DimType					fDimType;
	
	// Used for unpacked_dimension, packed_dimension, queue_dimension (when upper bound specified)
	public SVDBExpr					fExpr;
	
	// Used for associative_dimension when a type is specified
	public SVDBTypeInfo				fTypeInfo;

	public SVDBVarDimItem() {
		super(SVDBItemType.VarDimItem);
	}
	
	public void setDimType(DimType type) {
		fDimType = type;
	}

	public DimType getDimType() {
		return fDimType; 
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public void setTypeInfo(SVDBTypeInfo type_info) {
		fTypeInfo = type_info;
	}
	
	public String toString() {
		String ret = "[";
	
		if (fDimType != null) {
			switch (fDimType) {
				case Associative:
					if (fTypeInfo != null) {
						ret += fTypeInfo.toString();
					}
					break;

			case Queue:
				ret += "$";
				break;

			case Sized: 
				if (fExpr != null) {
					ret += fExpr.toString();
				}
				break;

			case Unsized:
				break;
			}
		}
		
		ret += "]";
		
		return ret;
	}
}

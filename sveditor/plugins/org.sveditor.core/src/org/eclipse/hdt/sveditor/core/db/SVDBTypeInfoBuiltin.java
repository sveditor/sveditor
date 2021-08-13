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


package org.eclipse.hdt.sveditor.core.db;

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDimItem;


public class SVDBTypeInfoBuiltin extends SVDBTypeInfo {
	public static final int				TypeAttr_Signed				= (1 << 7);
	public static final int				TypeAttr_Unsigned			= (1 << 8);

	public int						fAttr;
	public List<SVDBVarDimItem>		fVectorDim;
	
	public SVDBTypeInfoBuiltin() {
		this("");
	}
	
	public SVDBTypeInfoBuiltin(String typename) {
		super(typename, SVDBItemType.TypeInfoBuiltin);
	}

	public SVDBTypeInfoBuiltin(String typename, SVDBItemType type) {
		super(typename, type);
	}

	public int getAttr() {
		return fAttr;
	}
	
	public void setAttr(int attr) {
		fAttr = attr;
	}
	
	public List<SVDBVarDimItem> getVectorDim() {
		return fVectorDim;
	}
	
	public void setVectorDim(List<SVDBVarDimItem> dim) {
		fVectorDim = dim;
	}
	
	public String toString() {
		String ret = getName();
		
		if ((getAttr() & TypeAttr_Unsigned) != 0) {
			ret += " unsigned";
		}
	
		if (getVectorDim() != null && getVectorDim().size() > 0) {
			for (SVDBVarDimItem dim : getVectorDim()) {
				ret += dim.toString();
			}
		} 

		if (getArrayDim() != null && getArrayDim().size() > 0) {
			for (SVDBVarDimItem dim : getArrayDim()) {
				ret += dim.toString();
			}
		}
		
		return ret;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoBuiltin) {
			SVDBTypeInfoBuiltin o = (SVDBTypeInfoBuiltin)obj;
			
			if (fAttr != o.fAttr) {
				return false;
			}
			
			if (fVectorDim == null || o.fVectorDim == null) {
				if (fVectorDim != o.fVectorDim) {
					return false;
				}
			} else if (!fVectorDim.equals(o.fVectorDim)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}

	@Override
	public SVDBTypeInfoBuiltin duplicate() {
		SVDBTypeInfoBuiltin ret = new SVDBTypeInfoBuiltin(getName());
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		SVDBTypeInfoBuiltin o = (SVDBTypeInfoBuiltin)other;
		
		setAttr(o.getAttr());
		setVectorDim(o.getVectorDim());
	}

}

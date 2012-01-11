/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;

import java.util.List;

import net.sf.sveditor.core.db.stmt.SVDBVarDimItem;

public class SVDBTypeInfo extends SVDBItem implements ISVDBNamedItem {
	public static final int				TypeAttr_Vectored			= (1 << 6);
	List<SVDBVarDimItem>				fArrayDim;
	
	public SVDBTypeInfo(String typename, SVDBItemType data_type) {
		super(typename, data_type);
		fLocation = null;
	}

	@Deprecated
	public SVDBItemType getDataType() {
		return getType();
	}
	
	@Deprecated
	public void setDataType(SVDBItemType type) {
		setType(type);
	}
	
	public List<SVDBVarDimItem> getArrayDim() {
		return fArrayDim;
	}
	
	public void setArrayDim(List<SVDBVarDimItem> dim) {
		fArrayDim = dim;
	}
	
	@Override
	public SVDBTypeInfo duplicate() {
		return (SVDBTypeInfo)super.duplicate();
	}
	
	public static boolean isDataType(SVDBItemType type) {
		return false;
	}
	
}

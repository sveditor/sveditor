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


package net.sf.sveditor.core.scanner;

import java.util.List;

public class SVTypeInfo {
	public boolean						fEnumType 	= false;
	public boolean						fStructType = false;
	public boolean						fClassType  = false;
	public boolean						fModIfc   	= false;
	public List<SVEnumVal>				fEnumVals;
	public String						fTypeName;
	public String						fVectorDim;
	public int							fTypeQualifiers;
	public List<SVClassIfcModParam>		fParameters;
	
}

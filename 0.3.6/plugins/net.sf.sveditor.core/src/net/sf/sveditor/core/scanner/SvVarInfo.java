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

public class SvVarInfo {
	public static final int		Attr_FixedArray       = (1 << 0);
	public static final int		Attr_DynamicArray     = (1 << 1);
	public static final int		Attr_Queue     		  = (1 << 2);
	public static final int		Attr_AssocArray		  = (1 << 3);
	public static final int		Attr_ModIfc			  = (1 << 4);


	public String				fName;
	public int					fAttr;
	
	// Contains the array dimension/key for:
	// - fixed-size array
	// - associative array
	public String				fArrayDim;

}

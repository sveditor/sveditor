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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class SVDBParamPortDecl extends SVDBVarDeclStmt {
	public static final int			Direction_Ref     = (1 << 19);
	public static final int			Direction_Const   = (1 << 20);
	public static final int			Direction_Var     = (1 << 21);
	public static final int			Direction_Input   = (1 << 16);
	public static final int			Direction_Output  = (1 << 17);
	public static final int			Direction_Inout   = (1 << 18);
	public static final int			WireType_Shift    = 20;
	public static final int			WireType_none     = (0 << WireType_Shift); 
	public static final int			WireType_supply0  = (1 << WireType_Shift); 
	public static final int			Direction_supply1 = (2 << WireType_Shift); 
	public static final int			Direction_tri     = (3 << WireType_Shift); 
	public static final int			Direction_triand  = (4 << WireType_Shift); 
	public static final int			Direction_trior   = (5 << WireType_Shift); 
	public static final int			Direction_trireg  = (6 << WireType_Shift); 
	public static final int			Direction_tri0    = (7 << WireType_Shift); 
	public static final int			Direction_tri1    = (8 << WireType_Shift); 
	public static final int			Direction_uwire   = (9 << WireType_Shift); 
	public static final int			Direction_wire    = (10 << WireType_Shift); 
	public static final int			Direction_wand    = (11 << WireType_Shift);
	public static final int			Direction_wor     = (12 << WireType_Shift);
	
	private int						fDir;

	public SVDBParamPortDecl() {
		super(SVDBItemType.ParamPortDecl, null, 0);
	}
	
	public SVDBParamPortDecl(SVDBTypeInfo type) {
		super(SVDBItemType.ParamPortDecl, type, 0);
		fDir = Direction_Input;
	}
	
	public void setDir(int dir) {
		fDir = dir;
	}
	
	public int getDir() {
		return fDir;
	}
	
	public int getWireType() {
		return (fDir & (0xF << WireType_Shift));
	}
	
	public SVDBParamPortDecl duplicate() {
		SVDBParamPortDecl ret = new SVDBParamPortDecl(fTypeInfo);
		
		init(ret);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		fDir = ((SVDBParamPortDecl)other).fDir; 
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBParamPortDecl) {
			SVDBParamPortDecl o = (SVDBParamPortDecl)obj;

			if (o.fDir != fDir) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}
	
}

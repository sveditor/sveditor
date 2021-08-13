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


package org.eclipse.hdt.sveditor.core.db.stmt;

import org.eclipse.hdt.sveditor.core.db.SVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfo;

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
	
	public int						fDir;

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
		return (SVDBParamPortDecl)super.duplicate();
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

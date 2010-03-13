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

public interface IFieldItemAttr {
	int	FieldAttr_Local     		= (1 << 0);
	int	FieldAttr_Protected 		= (1 << 1);
	int FieldAttr_Rand				= (1 << 2);
	int FieldAttr_Randc				= (1 << 3);
	int FieldAttr_Static            = (1 << 4);
	int FieldAttr_Virtual			= (1 << 5);
	int FieldAttr_Automatic         = (1 << 6);
	int FieldAttr_Extern            = (1 << 7);
	int FieldAttr_Const             = (1 << 8);
	int FieldAttr_DPI				= (1 << 9);
	int FieldAttr_Pure				= (1 << 10);
	int FieldAttr_Context			= (1 << 11);
	// Flag for built-in fields that must be provided as content
	// assist in all contexts (eg options field in covergroup) 
	int FieldAttr_SvBuiltinGlobal	= (1 << 12);
	
	
	void setAttr(int attr);
	
	int getAttr();

}

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
	// Flag for built-in objects. 
	int FieldAttr_SvBuiltin			= (1 << 12);
	int FieldAttr_Interface			= (1 << 13);
	
	void setAttr(int attr);
	
	int getAttr();

}

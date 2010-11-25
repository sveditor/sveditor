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

public enum SVDBItemType {
	NULL,
	File,
	Module,
	Class,
	Interface,
	Program,
	Struct,
	Task,
	Function,
	VarDecl,
	ModIfcInst,
	TaskFuncParam,
	Macro,
	PreProcCond,
	Include,
	PackageDecl,
	Covergroup,
	Coverpoint,
	CoverpointCross,
	Sequence,
	Property,
	ModIfcClassParam,
	Constraint,
	Typedef,
	TypeInfo,
	InitialBlock,
	AlwaysBlock,
	Assign,
	Marker,
	ParamValue,
	ParamValueList,
	GenerateBlock,
	ClockingBlock
}

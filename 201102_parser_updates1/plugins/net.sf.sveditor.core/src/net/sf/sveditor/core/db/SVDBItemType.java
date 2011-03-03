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
	Id,
	File,
	Module,
	Class,
	Interface,
	Program,
	Struct,
	Task,
	Function,
	ModIfcInst,
	Macro,
	PreProcCond,
	Include,
	PackageDecl,
	Covergroup,
	Coverpoint,
	CoverpointBins,
	CoverCross,
	CoverCrossBinsSel,
	Sequence,
	Property,
	ModIfcClassParam,
	Constraint,
	TypeInfo,
	InitialBlock,
	AlwaysBlock,
	Assign,
	Marker,
	ParamValue,
	ParamValueList,
	GenerateBlock,
	ClockingBlock,
	Import,
	Expr,

	// Statement items
	ActionBlockStmt,
	LabeledStmt,
	BlockStmt,
	DisableStmt,
	DisableForkStmt,
	EventControlStmt,
	NullStmt,
	WhileStmt,
	DelayControlStmt,
	DoWhileStmt,
	ExprStmt,
	ForStmt,
	ForeachStmt,
	RepeatStmt,
	ForeverStmt,
	IfStmt,
	ForkStmt,
	CaseStmt,
	CaseItem,
	AssertStmt,
	WaitStmt,
	WaitForkStmt,
	WaitOrderStmt,
	ReturnStmt,
	BreakStmt,
	ContinueStmt,
	EventTriggerStmt,
	
	VarDeclStmt,
	VarDeclItem,
	VarDimItem,	
	ParamPortDecl,
	
	TypedefStmt,
	TypedefItem,
	
	CoverageOptionStmt,

	;
	
	public boolean isElemOf(SVDBItemType ... type_list) {
		if (type_list.length == 0) {
			return true;
		}
		for (SVDBItemType t : type_list) {
			if (this == t) {
				return true;
			}
		}
		return false;
	}
}

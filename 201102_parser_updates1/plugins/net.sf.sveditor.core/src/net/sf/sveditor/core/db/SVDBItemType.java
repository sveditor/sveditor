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

import java.util.HashMap;
import java.util.Map;

@SuppressWarnings("rawtypes")
public enum SVDBItemType {
	Identifier,
	File,
	ModuleDecl,
	ClassDecl,
	InterfaceDecl,
	ProgramDecl,
	Task,
	Function,
	ModIfcInst,
	MacroDef,
	PreProcCond,
	Include,
	PackageDecl,
	Covergroup,
	Coverpoint,
	CoverpointBins,
	CoverpointCross,
	CoverCrossBinsSel,
	Sequence,
	Property,
	ModIfcClassParam,
	Constraint,
	Assign,
	Marker,
	ParamValueAssign,
	ParamValueAssignList,
	GenerateBlock,
	GenerateFor,
	GenerateIf,
	GenerateRegion,
	ClockingBlock,
	
	// Data Types
	TypeInfoBuiltin,
	TypeInfoBuiltinNet,
	TypeInfoClassItem,
	TypeInfoClassType,
	TypeInfoEnum,
	TypeInfoFwdDecl,
	TypeInfoStruct,
	TypeInfoUserDef,
	TypeInfoModuleIfc,

	// Statement items
	ActionBlockStmt,
	AlwaysStmt,
	AssertStmt,
	AssignStmt,
	AssumeStmt,
	LabeledStmt,
	BlockStmt,
	ConstraintDistListStmt,
	ConstraintDistListItem,
	ConstraintForeachStmt,
	ConstraintIfStmt,
	ConstraintImplStmt,
	ConstraintSetStmt,
	ConstraintSolveBeforeStmt,
	DisableStmt,
	DisableForkStmt,
	DelayControlStmt,
	DoWhileStmt,
	EventControlStmt,
	ExportStmt,
	ExprStmt,
	FinalStmt,
	ForStmt,
	ForeachStmt,
	ForeverStmt,
	NullStmt,
	ProceduralContAssignStmt,
	WhileStmt,
	RepeatStmt,
	IfStmt,
	ImportStmt,
	InitialStmt,
	ForkStmt,
	CaseStmt,
	CaseItem,
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

	// Expressions
	ClockingEventExpr,
	ArrayAccessExpr,
	AssignExpr,
	BinaryExpr,
	CastExpr,
	CondExpr,
	CtorExpr,
	FieldAccessExpr,
	IdentifierExpr,
	IncDecExpr,
	LiteralExpr,
	NullExpr,
	ParenExpr,
	InsideExpr,
	RangeExpr,
	RangeDollarBoundExpr,
	QualifiedSuperFieldRefExpr,
	QualifiedThisRefExpr,
	TFCallExpr,
	RandomizeCallExpr,
	UnaryExpr,
	
	NamedArgExpr, // .ARG(value)
	
	ConcatenationExpr,
	StringExpr,
	AssignmentPatternExpr,
	AssignmentPatternRepeatExpr,
	
	CoverpointExpr,
	CoverBinsExpr,

	ThisExpr,
	SuperExpr,
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
	
	public static final Map<SVDBItemType, Class>		fObjectMap;
	
	static {
		fObjectMap = new HashMap<SVDBItemType, Class>();
		fObjectMap.put(File, SVDBFile.class);
		fObjectMap.put(ModuleDecl, SVDBModIfcDecl.class);		
	}
	
}

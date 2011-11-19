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
	File,
	ModuleDecl,
	ClassDecl,
	InterfaceDecl,
	ProgramDecl,
	Task,
	Function,
	ModIfcInst,
	ModIfcInstItem,
	ModportDecl,
	ModportItem,
	ModportSimplePortsDecl,
	ModportSimplePort,
	ModportClockingPortDecl,
	ModportTFPortsDecl,
	ModportTFPort,
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
	TypeInfoUnion,	
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
	CoverStmt,
	DisableStmt,
	DisableForkStmt,
	DefParamStmt,
	DefParamItem,
	DelayControlStmt,
	DoWhileStmt,
	EventControlStmt,
	ExportStmt,
	ExportItem,
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
	ImportItem,
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
	
	CoverageOptionStmt,
	CoverageCrossBinsSelectStmt,
	TimePrecisionStmt,
	TimeUnitsStmt,

	// Expressions
	ArrayAccessExpr,
	AssignExpr,
	AssignmentPatternExpr,
	AssignmentPatternRepeatExpr,
	AssociativeArrayElemAssignExpr,
	BinaryExpr,
	CastExpr,
	ClockingEventExpr,
	ConcatenationExpr,
	CondExpr,
	CrossBinsSelectConditionExpr,
	CtorExpr,
	CycleDelayExpr,
	FieldAccessExpr,
	FirstMatchExpr,
	IdentifierExpr,
	IncDecExpr,
	InsideExpr,
	LiteralExpr,
	NamedArgExpr, // .ARG(value)
	NullExpr,
	ParenExpr,
	PropertyWeakStrongExpr,
	RandomizeCallExpr,
	RangeDollarBoundExpr,
	RangeExpr,
	TFCallExpr,
	UnaryExpr,
	TypeExpr,
	NameMappedExpr,
	
	// Property Expression Types
	PropertySpecExpr,
	
	SequenceCycleDelayExpr,
	SequenceClockingExpr,
	SequenceMatchItemExpr,
	SequenceDistExpr,
	SequenceRepetitionExpr,	
	StringExpr,
	
	CoverpointExpr,
	CoverBinsExpr,
	;
	
	public boolean isElemOf(SVDBItemType ... type_list) {
		switch (type_list.length) {
			case 0: return true;
			case 1: return (type_list[0] == this);
			case 2: return (type_list[0] == this || type_list[1] == this);
			case 3: return (type_list[0] == this || type_list[1] == this ||
							type_list[2] == this);
			case 4: return (type_list[0] == this || type_list[1] == this ||
							type_list[2] == this || type_list[3] == this);
			default:
				for (SVDBItemType t : type_list) {
					if (this == t) {
						return true;
					}
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

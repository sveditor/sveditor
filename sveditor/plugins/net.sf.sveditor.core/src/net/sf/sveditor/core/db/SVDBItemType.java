/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import java.util.Set;

@SuppressWarnings("rawtypes")
public enum SVDBItemType {
	File,
	FileTree,
	FileTreeMacroList,
	ModuleDecl,
	ClassDecl,
	ConfigDecl,
	InterfaceDecl,
	ProgramDecl,
	Bind,
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
	MacroDefParam,
	PreProcCond,
	// Marks a region of the file that was not processed, due to
	// preprocessor macros
	UnprocessedRegion, 
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
	AssignItem,
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
	TypeInfoEnumerator,
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
	BreakStmt,
	CaseItem,
	CaseStmt,
	ConfigCellClauseStmt,
	ConfigDefaultClauseStmt,
	ConfigDesignStmt,
	ConfigInstClauseStmt,
	ConstraintDistListStmt,
	ConstraintDistListItem,
	ConstraintForeachStmt,
	ConstraintIfStmt,
	ConstraintImplStmt,
	ConstraintSetStmt,
	ConstraintSolveBeforeStmt,
	ContinueStmt,
	CoverStmt,
	DisableStmt,
	DisableForkStmt,
	DefParamStmt,
	DefParamItem,
	DelayControlStmt,
	DoWhileStmt,
	EventControlStmt,
	EventTriggerStmt,
	ExportStmt,
	ExportItem,
	ExprStmt,
	FinalStmt,
	ForeachStmt,
	ForeverStmt,
	ForkStmt,
	ForStmt,
	IfStmt,
	ImportItem,
	ImportStmt,
	InitialStmt,
	NullStmt,
	ProceduralContAssignStmt,
	RepeatStmt,
	ReturnStmt,
	VarDeclItem,
	VarDeclStmt,
	WaitForkStmt,
	WaitOrderStmt,
	WaitStmt,
	WhileStmt,
	
	
	
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
	AssociativeArrayAssignExpr,
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
	ForeachLoopvarExpr,
	IdentifierExpr,
	IncDecExpr,
	InsideExpr,
	LiteralExpr,
	MinTypMaxExpr,
	NamedArgExpr, // .ARG(value)
	NameMappedExpr,
	NullExpr,
	OpenRangeListExpr,
	ParamIdExpr,	
	ParenExpr,
	PropertyWeakStrongExpr,
	RandomizeCallExpr,
	RangeDollarBoundExpr,
	RangeExpr,
	TFCallExpr,
	UnaryExpr,
	TypeExpr,
	
	// Property Expression Types
	PropertySpecExpr,
	PropertyIfStmt,
	PropertyCaseStmt,
	PropertyCaseItem,
	
	SequenceCycleDelayExpr,
	SequenceClockingExpr,
	SequenceMatchItemExpr,
	SequenceDistExpr,
	SequenceRepetitionExpr,	
	StringExpr,
	
	CoverpointExpr,
	CoverBinsExpr,
	
	// Documentation types
	DocComment,
	
	// Argument-File Tokens
	ArgFileIncDirStmt,
	ArgFilePathStmt,
	ArgFileDefineStmt,
	ArgFileForceSvStmt,
	ArgFileIncFileStmt,
	ArgFileMfcuStmt,
	ArgFileSrcLibPathStmt,
	ArgFileSrcLibFileStmt,
	ArgFileLibExtStmt,
	
	
	//***************************************************************
	//* VHDL Types
	//***************************************************************
//	VHEntityDecl
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
	
	public boolean isElemOf(Set<SVDBItemType> types) {
		return types.contains(this);
	}
	
	public static final Map<SVDBItemType, Class>		fObjectMap;
	
	static {
		fObjectMap = new HashMap<SVDBItemType, Class>();
		fObjectMap.put(File, SVDBFile.class);
		fObjectMap.put(ModuleDecl, SVDBModIfcDecl.class);		
	}
	
}

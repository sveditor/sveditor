/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.stmt.ISVDBBodyStmt;
import net.sf.sveditor.core.db.stmt.SVDBActionBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBCaseItem;
import net.sf.sveditor.core.db.stmt.SVDBCaseStmt;
import net.sf.sveditor.core.db.stmt.SVDBDoWhileStmt;
import net.sf.sveditor.core.db.stmt.SVDBExprStmt;
import net.sf.sveditor.core.db.stmt.SVDBForStmt;
import net.sf.sveditor.core.db.stmt.SVDBIfStmt;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBImportStmt;
import net.sf.sveditor.core.db.stmt.SVDBRepeatStmt;
import net.sf.sveditor.core.db.stmt.SVDBReturnStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitStmt;
import net.sf.sveditor.core.db.stmt.SVDBWhileStmt;

public abstract class AbstractSVDBFileRefFinder {
	protected SVDBFile						fFile;
	protected Stack<ISVDBChildItem>		fScopeStack;
	
	public AbstractSVDBFileRefFinder() {
		fScopeStack = new Stack<ISVDBChildItem>();
	}
	
	public void visitFile(SVDBFile file) {
		fFile = file;
		fScopeStack.push(fFile);
		visitChildParent(fFile);
		fScopeStack.pop();
	}
	
	protected void visitChildParent(ISVDBChildParent parent) {
		for (ISVDBChildItem c : parent.getChildren()) {
			visitChild(c);
		}
	}
	
	protected void visitChild(ISVDBChildItem c) {
		fScopeStack.push(c);
		if (c instanceof SVDBStmt) {
			visitStmt((SVDBStmt)c);
		} else if (c instanceof SVDBExpr) {
			visitExpr((SVDBExpr)c);
		} else {
			switch (c.getType()) {
				// Nothing to do at this level. 
				case BlockStmt:
				case BreakStmt:
				case CaseItem:
				case ModuleDecl:
				case InterfaceDecl:
				case ProgramDecl:
				case Task:
				case Function:
					break;

				case Include: {
					SVDBInclude inc = (SVDBInclude)c;
					visitRef(inc.getLocation(), SVDBRefType.IncludeReference, inc.getName());
				} break;

				// Class may have a super-class, in addition
				// to body items
				case ClassDecl: {
					SVDBClassDecl cls = (SVDBClassDecl)c;
					if (cls.getSuperClass() != null) {
						SVDBTypeInfoClassType cls_t = cls.getSuperClass();
						visitRef(null, SVDBRefType.TypeReference, cls_t.getName());
					}
				} break;
				
				case ModIfcInst: {
					SVDBModIfcInst inst = (SVDBModIfcInst)c;
				} break;
				
				default: {
					break;
				}
			}
			if (c instanceof ISVDBChildParent) {
				visitChildParent((ISVDBChildParent)c);
			}
		}
		
		fScopeStack.pop();
	}
	
	protected void visitStmt(SVDBStmt stmt) {
		if (stmt == null) {
			return;
		}
		switch (stmt.getType()) {
			case ActionBlockStmt: {
				SVDBActionBlockStmt action_blk = (SVDBActionBlockStmt)stmt;
				if (action_blk.getStmt() != null) {
					fScopeStack.push(action_blk.getStmt());
					visitStmt(action_blk.getStmt());
					fScopeStack.pop();
				}
				if (action_blk.getElseStmt() != null) {
					fScopeStack.push(action_blk.getElseStmt());
					visitStmt(action_blk.getElseStmt());
					fScopeStack.pop();
				}
				} break;
				
			case AlwaysStmt: {
				/** TODO:
				SVDBAlwaysStmt a_stmt = (SVDBAlwaysStmt)stmt;
				a_stmt.get
				 */
				} break;
				/*
				AssertStmt,
				 */
				
			case AssignStmt: {
				// TODO:
				} break;
				
				/*
				AssumeStmt,
				 */
				
				// Nothing to do here
				// case LabeledStmt: break;
				
				case BlockStmt: {
					SVDBBlockStmt block = (SVDBBlockStmt)stmt;
					for (ISVDBChildItem ci : block.getChildren()) {
						visitStmt((SVDBStmt)ci);
					}
					} break;
					
				// Ignore
				// case BreakStmt:

				case CaseItem: {
					SVDBCaseItem ci = (SVDBCaseItem)stmt;
					for (SVDBExpr expr : ci.getExprList()) {
						visitExpr(expr);
					}
					
					// visitStmt(ci.getBody());
					} break;
				
				case CaseStmt: {
					SVDBCaseStmt case_stmt = (SVDBCaseStmt)stmt;
					
					visitExpr(case_stmt.getExpr());
					
					for (SVDBCaseItem ci : case_stmt.getCaseItemList()) {
						visitStmt(ci);
					}
					} break;
				/* TODO:
				ConstraintDistListStmt,
				ConstraintDistListItem,
				ConstraintForeachStmt,
				ConstraintIfStmt,
				ConstraintImplStmt,
				ConstraintSetStmt,
				ConstraintSolveBeforeStmt,
				 */
				// Ignore
				// case ContinueStmt:
				/* TODO:
				CoverStmt,
				DisableStmt,
				DisableForkStmt,
				DefParamStmt,
				DefParamItem,
				DelayControlStmt,
				 */
				case DoWhileStmt: {
					SVDBDoWhileStmt dw_stmt = (SVDBDoWhileStmt)stmt;
					visitExpr(dw_stmt.getCond());
					} break;
				/* TODO:
				EventControlStmt,
				EventTriggerStmt,
				ExportStmt,
				ExportItem,
				*/
				
				case ExprStmt: {
					SVDBExprStmt expr_stmt = (SVDBExprStmt)stmt;
					fScopeStack.push(expr_stmt);
					visitExpr(expr_stmt.getExpr());
					fScopeStack.pop();
					} break;
				
				/*
				FinalStmt,
				ForeachStmt,
				 */
				// Ignore
				// case ForeverStmt:
				/*
				ForkStmt,
				 */
				
				case ForStmt: {
					SVDBForStmt f_stmt = (SVDBForStmt)stmt;
					if (f_stmt.getInitExpr() != null) {
						visitStmt(f_stmt.getInitExpr());
					}
					if (f_stmt.getTestExpr() != null) {
						visitStmt(f_stmt.getTestExpr());
					}
					if (f_stmt.getIncrStmt() != null) {
						visitStmt(f_stmt.getIncrStmt());
					}
					} break;
					
				case IfStmt: {
					SVDBIfStmt if_stmt = (SVDBIfStmt)stmt;
					visitExpr(if_stmt.getCond());
					visitStmt(if_stmt.getIfStmt());
					
					if (if_stmt.getElseStmt() != null) {
						visitStmt(if_stmt.getElseStmt());
					}
					} break;


				case ImportItem: {
					SVDBImportItem i_stmt = (SVDBImportItem)stmt;
					// TODO: simplify import statement?
					visitRef(i_stmt.getLocation(), SVDBRefType.ImportReference, i_stmt.getImport());
					} break;
					
				case ImportStmt: {
					SVDBImportStmt i_stmt = (SVDBImportStmt)stmt;
					for (ISVDBChildItem ci : i_stmt.getChildren()) {
						visitStmt((SVDBStmt)ci);
					}
					} break;
					
				// Nothing to do here
				// case InitialStmt: 
				// case NullStmt:
				 /*
				ProceduralContAssignStmt,
				 */
				case RepeatStmt: {
					SVDBRepeatStmt r_stmt = (SVDBRepeatStmt)stmt;
					visitExpr(r_stmt.getExpr());
					} break;
					
				case ReturnStmt: {
					SVDBReturnStmt r_stmt = (SVDBReturnStmt)stmt;
					if (r_stmt.getExpr() != null) {
						visitExpr(r_stmt.getExpr());
					}
					} break;
				
				case VarDeclStmt: {
					SVDBVarDeclStmt var_decl = (SVDBVarDeclStmt)stmt;
					if (var_decl.getTypeInfo().getType() == SVDBItemType.TypeInfoUserDef) {
						SVDBTypeInfoUserDef ut = (SVDBTypeInfoUserDef)var_decl.getTypeInfo();
						visitRef(null, SVDBRefType.TypeReference, ut.getName());

						for (ISVDBChildItem var_item_c : var_decl.getChildren()) {
							SVDBVarDeclItem var_item = (SVDBVarDeclItem)var_item_c;
							if (var_item.getInitExpr() != null) {
								// TODO: process the expression to pull out field/var references
							}
						}
					}
					} break;

				/* TODO:
				WaitForkStmt,
				WaitOrderStmt,
				 */
				case WaitStmt: {
					SVDBWaitStmt w_stmt = (SVDBWaitStmt)stmt;
					visitExpr(w_stmt.getExpr());
					} break;
					
				case WhileStmt: {
					SVDBWhileStmt w_stmt = (SVDBWhileStmt)stmt;
					visitExpr(w_stmt.getExpr());
					} break;
				default: {
					break;
				}
		}
		
		if (stmt instanceof ISVDBBodyStmt) {
			ISVDBBodyStmt b_stmt = (ISVDBBodyStmt)stmt;
			if (b_stmt.getBody() != null) {
				visitStmt(b_stmt.getBody());
			}
		}
	}
	
	protected void visitExpr(SVDBExpr expr) {
		// Bail in case we get called by mistake
		if (expr == null) {
			return;
		}
		
		switch (expr.getType()) {
		/*
		ArrayAccessExpr,
		 */
		
			case AssignExpr: {
				SVDBAssignExpr a_expr = (SVDBAssignExpr)expr;
				visitExpr(a_expr.getLhs());
				visitExpr(a_expr.getRhs());
				} break;
		/*
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
		 */
		
			case FieldAccessExpr: {
				SVDBFieldAccessExpr f_expr = (SVDBFieldAccessExpr)expr;
				visitExpr(f_expr.getExpr());
				visitExpr(f_expr.getLeaf());
				} break;
		/*
		FirstMatchExpr,
		 */
			case IdentifierExpr: {
				SVDBIdentifierExpr id_expr = (SVDBIdentifierExpr)expr;
				visitRef(id_expr.getLocation(), SVDBRefType.FieldReference, id_expr.getId());
				} break;
		/*
		IncDecExpr,
		InsideExpr,
		LiteralExpr,
		NamedArgExpr, // .ARG(value)
		NullExpr,
		ParamIdExpr,	
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
		 */
			default: {
				break;
			}
		}
	}
	
	protected void visitRef(SVDBLocation loc, SVDBRefType type, String name) {
		System.out.println("reference: " + type + " : " + name);
	}

}

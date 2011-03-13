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


package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.stmt.SVDBActionBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssignStmt;
import net.sf.sveditor.core.db.stmt.SVDBBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBBreakStmt;
import net.sf.sveditor.core.db.stmt.SVDBCaseItem;
import net.sf.sveditor.core.db.stmt.SVDBCaseStmt;
import net.sf.sveditor.core.db.stmt.SVDBCaseStmt.CaseType;
import net.sf.sveditor.core.db.stmt.SVDBContinueStmt;
import net.sf.sveditor.core.db.stmt.SVDBDelayControlStmt;
import net.sf.sveditor.core.db.stmt.SVDBDisableForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBDisableStmt;
import net.sf.sveditor.core.db.stmt.SVDBDoWhileStmt;
import net.sf.sveditor.core.db.stmt.SVDBEventControlStmt;
import net.sf.sveditor.core.db.stmt.SVDBEventTriggerStmt;
import net.sf.sveditor.core.db.stmt.SVDBExprStmt;
import net.sf.sveditor.core.db.stmt.SVDBForStmt;
import net.sf.sveditor.core.db.stmt.SVDBForeachStmt;
import net.sf.sveditor.core.db.stmt.SVDBForeverStmt;
import net.sf.sveditor.core.db.stmt.SVDBForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBForkStmt.JoinType;
import net.sf.sveditor.core.db.stmt.SVDBIfStmt;
import net.sf.sveditor.core.db.stmt.SVDBLabeledStmt;
import net.sf.sveditor.core.db.stmt.SVDBNullStmt;
import net.sf.sveditor.core.db.stmt.SVDBProceduralContAssignStmt;
import net.sf.sveditor.core.db.stmt.SVDBProceduralContAssignStmt.AssignType;
import net.sf.sveditor.core.db.stmt.SVDBRepeatStmt;
import net.sf.sveditor.core.db.stmt.SVDBReturnStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitStmt;
import net.sf.sveditor.core.db.stmt.SVDBWhileStmt;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVBehavioralBlockParser extends SVParserBase {
	
	public static boolean isDeclAllowed(SVDBStmt stmt) {
		return (stmt.getType() == SVDBItemType.VarDeclStmt || 
				stmt.getType() == SVDBItemType.TypedefStmt);
	}
	
	public SVBehavioralBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBStmt statement() throws SVParseException {
		return statement(false, true);
	}
	
	public SVDBStmt statement(boolean decl_allowed, boolean ansi_decl) throws SVParseException {
		return statement(decl_allowed, ansi_decl, "", 0);
	}
	
	private SVDBStmt statement(String parent, int level) throws SVParseException {
		return statement(false, false, parent, level);
	}
	
	private static final Set<String> fDeclKeywordsANSI;
	private static final Set<String> fDeclKeywordsNonANSI;
	
	static {
		fDeclKeywordsANSI = new HashSet<String>();
		fDeclKeywordsNonANSI = new HashSet<String>();
		
		fDeclKeywordsANSI.add("const");
		fDeclKeywordsANSI.add("var");
		fDeclKeywordsANSI.add("automatic");
		fDeclKeywordsANSI.add("static");
		fDeclKeywordsANSI.add("typedef");
		
		fDeclKeywordsNonANSI.addAll(fDeclKeywordsANSI);
		fDeclKeywordsNonANSI.add("input");
		fDeclKeywordsNonANSI.add("output");
		fDeclKeywordsNonANSI.add("inout");
		fDeclKeywordsNonANSI.add("ref");
	}
	
	private SVDBStmt statement(boolean decl_allowed, boolean ansi_decl, String parent, int level) throws SVParseException {
		debug("--> [" + level + "] parent=" + parent + " statement " + 
				fLexer.peek() + " @ " + fLexer.getStartLocation().getLine() + " decl_allowed=" + decl_allowed);
		SVDBStmt stmt = null;
		Set<String> decl_keywords = (ansi_decl)?fDeclKeywordsANSI:fDeclKeywordsNonANSI;

		// Try for a declaration here
		if (fLexer.peekKeyword(decl_keywords) ||
				(fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void")) ||
				fLexer.isIdentifier() || fLexer.peekKeyword("typedef")) {
			boolean builtin_type = (fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void"));
			
			if (fLexer.peekKeyword(decl_keywords) || 
					(fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void")) ||
					fLexer.peekKeyword("typedef")) {
				// Definitely a declaration
				if (!decl_allowed) {
					error("declaration in a post-declaration location");
				}
				SVDBStmt decl = parsers().blockItemDeclParser().parse();
				return decl;
			} else {
				// May be a declaration. Let's see
				
				// Variable declarations
				List<SVToken> id_list = parsers().SVParser().scopedStaticIdentifier_l(true);
			
				if (!builtin_type && 
					((fLexer.peekKeyword() && !fLexer.peekKeyword(fDeclKeywordsNonANSI)) ||
							(fLexer.peekOperator() && !fLexer.peekOperator("#")))) {
					// likely a statement
					for (int i=id_list.size()-1; i>=0; i--) {
						fLexer.ungetToken(id_list.get(i));
					}
					debug("non-declaration statement: " + fLexer.peek());
				} else {
					for (int i=id_list.size()-1; i>=0; i--) {
						fLexer.ungetToken(id_list.get(i));
					}
					debug("Pre-var parse: " + fLexer.peek());
					if (!decl_allowed) {
						error("declaration in a non-declaration location");
					}
					
					SVDBStmt decl = parsers().blockItemDeclParser().parse();
					
				
					// Bail for now
					return decl; 
				}
			}
		} else {
			
			// time to move on to the body
			debug("non-declaration statement: " + fLexer.peek());
		}

		if (fLexer.peekKeyword("begin")) {
			SVDBBlockStmt block = new SVDBBlockStmt();
			// Declarations are permitted at block-start
			decl_allowed = true;
			fLexer.eatToken();
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
				SVDBStmt tmp = statement(decl_allowed, true, parent, level+1);
				decl_allowed = isDeclAllowed(tmp);
				block.addStmt(tmp);
			}
			fLexer.readKeyword("end");
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			stmt = block;
		} else if (fLexer.peekKeyword("unique","unique0","priority")) {
			// TODO: ignore unique_priority for now
			fLexer.eatToken();
			// 'if' or 'case'
			stmt = statement();
		} else if (fLexer.peekKeyword("if")) {
			stmt = parse_if_stmt();
		} else if (fLexer.peekKeyword("while")) {
			fLexer.eatToken();
			fLexer.readOperator("(");
			SVDBWhileStmt while_stmt = new SVDBWhileStmt(parsers().exprParser().expression());
			fLexer.readOperator(")");
			
			while_stmt.setBody(statement("while", level));
			stmt = while_stmt;
		} else if (fLexer.peekKeyword("do")) {
			SVDBDoWhileStmt do_while = new SVDBDoWhileStmt();
			fLexer.eatToken();
			do_while.setBody(statement("do", level));
			fLexer.readKeyword("while");
			fLexer.readOperator("(");
			do_while.setCond(parsers().exprParser().expression());
			fLexer.readOperator(")");
			fLexer.readOperator(";");
			stmt = do_while;
		} else if (fLexer.peekKeyword("repeat")) {
			SVDBRepeatStmt repeat = new SVDBRepeatStmt();
			fLexer.eatToken();
			fLexer.readOperator("(");
			repeat.setExpr(parsers().exprParser().expression());
			fLexer.readOperator(")");
			repeat.setBody(statement("repeat", level));
			stmt = repeat;
		} else if (fLexer.peekKeyword("forever")) {
			fLexer.eatToken();
			SVDBForeverStmt forever = new SVDBForeverStmt();
			forever.setBody(statement("forever", level));
			stmt = forever;
		} else if (fLexer.peekKeyword("for")) {
			stmt = for_stmt(level);
		} else if (fLexer.peekKeyword("foreach")) {
			SVDBForeachStmt foreach = new SVDBForeachStmt();
			fLexer.eatToken();
			fLexer.readOperator("(");
			foreach.setCond(parsers().exprParser().expression());
			fLexer.readOperator(")");
			foreach.setBody(statement("foreach", level));
			
			stmt = foreach;
		} else if (fLexer.peekKeyword("fork")) {
			SVDBForkStmt fork = new SVDBForkStmt();
			decl_allowed = true;
			fLexer.eatToken();
			
			// Read block identifier
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			
			while (fLexer.peek() != null && 
					!fLexer.peekKeyword("join", "join_none", "join_any")) {
				debug("--> Fork Statement");
				// Allow declarations at the root of the fork
				SVDBStmt tmp = statement(decl_allowed, true, "fork", level);
				decl_allowed = isDeclAllowed(tmp);
				fork.addStmt(tmp);
				debug("<-- Fork Statement");
			}
			// Read join
			String join_type = fLexer.readKeyword("join", "join_none", "join_any");
			if (join_type.equals("join")) {
				fork.setJoinType(JoinType.Join);
			} else if (join_type.equals("join_none")) {
				fork.setJoinType(JoinType.JoinNone);
			} else if (join_type.equals("join_any")) {
				fork.setJoinType(JoinType.JoinAny);
			}
			
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			stmt = fork;
		} else if (fLexer.peekKeyword("case", "casex", "casez","randcase")) {
			stmt = parse_case_stmt();
		} else if (fLexer.peekKeyword("wait")) {
			SVDBWaitStmt wait_stmt;
			fLexer.eatToken();
			
			if (fLexer.peekKeyword("fork")) {
				wait_stmt = new SVDBWaitForkStmt();
				fLexer.eatToken();
				fLexer.readOperator(";");
			} else {
				wait_stmt = new SVDBWaitStmt();
				fLexer.readOperator("(");
				wait_stmt.setExpr(parsers().exprParser().expression());
				fLexer.readOperator(")");
				if (!fLexer.peekOperator(";")) {
					wait_stmt.setStmt(statement("wait", level));
				} else {
					fLexer.readOperator(";");
				}
			}
			stmt = wait_stmt;
		} else if (fLexer.peekOperator("->", "->>")) {
			SVDBEventTriggerStmt event_trigger = new SVDBEventTriggerStmt();
			String tt = fLexer.eatToken();
			
			// TODO: handle [delay_or_event_control] after ->>
			
			event_trigger.setHierarchicalEventIdentifier(parsers().exprParser().expression());
			stmt = event_trigger;
			fLexer.readOperator(";");
			stmt = event_trigger;
		} else if (fLexer.peekOperator("@")) {
			SVDBEventControlStmt event_stmt = new SVDBEventControlStmt();
			fLexer.eatToken();
			event_stmt.setExpr(parsers().exprParser().event_expression());

			// statement_or_null
			event_stmt.setStmt(statement(decl_allowed, ansi_decl));
			stmt = event_stmt;
		} else if (fLexer.peekOperator("#")) {
			SVDBLocation start = fLexer.getStartLocation();
			SVDBDelayControlStmt delay_stmt = new SVDBDelayControlStmt();
			delay_stmt.setLocation(start);
			
			delay_stmt.setExpr(fParsers.exprParser().delay_expr());
			delay_stmt.setStmt(statement(false, true));
			stmt = delay_stmt;
		} else if (fLexer.peekKeyword("disable")) {
			SVDBDisableStmt disable_stmt;
			fLexer.eatToken();
			if (fLexer.peekKeyword("fork")) {
				fLexer.eatToken();
				disable_stmt = new SVDBDisableForkStmt();
			} else {
				disable_stmt = new SVDBDisableStmt();
				disable_stmt.setHierarchicalId(parsers().exprParser().expression());
			}
			
			fLexer.readOperator(";");
			stmt = disable_stmt;
		} else if (fLexer.peekKeyword("end")) {
			// An unmatched 'end' signals that we're missing some
			// behavioral construct
			error("Unexpected 'end' without matching 'begin' in level " + parent);
		} else if (fLexer.peekKeyword("assert","assume")) {
			stmt = parsers().assertionParser().parse();
		} else if (fLexer.peekKeyword("return")) {
			SVDBReturnStmt return_stmt = new SVDBReturnStmt();
			
			debug("return statement");
			
			fLexer.eatToken();
			if (!fLexer.peekOperator(";")) {
				return_stmt.setExpr(parsers().exprParser().expression());
			}
			fLexer.readOperator(";");
			stmt = return_stmt;
		} else if (fLexer.peekKeyword("break")) {
			SVDBBreakStmt break_stmt = new SVDBBreakStmt();
			fLexer.eatToken();
			fLexer.readOperator(";");
			stmt = break_stmt;
		} else if (fLexer.peekKeyword("continue")) {
			SVDBContinueStmt continue_stmt = new SVDBContinueStmt();
			fLexer.eatToken();
			fLexer.readOperator(";");
			stmt = continue_stmt;
		} else if (fLexer.peekKeyword("assign", "deassign", "force", "release")) {
			stmt = procedural_cont_assign();
		} else if (ParserSVDBFileFactory.isFirstLevelScope(fLexer.peek(), 0) ||
			ParserSVDBFileFactory.isSecondLevelScope(fLexer.peek())) {
			error("Unexpected non-behavioral statement keyword " + fLexer.peek());
		} else if (fLexer.peekOperator(";")) {
			stmt = new SVDBNullStmt();
			fLexer.eatToken();
		} else if (fLexer.peekId() || 
				fLexer.peekKeyword(SVKeywords.fBuiltinTypes) ||
				fLexer.peekKeyword("this", "super") || 
				fLexer.peekOperator()) {
			SVToken id = fLexer.consumeToken();
			
			if (fLexer.peekOperator(":")) {
				// Labeled statement
				String label = id.getImage();
				fLexer.eatToken();
				stmt = new SVDBLabeledStmt(label, statement(decl_allowed, ansi_decl));
			} else {
				fLexer.ungetToken(id);

				// 
				SVDBExpr lvalue = parsers().exprParser().variable_lvalue();

				// If an assignment
				if (fLexer.peekOperator(SVKeywords.fAssignmentOps)) {
					String op = fLexer.eatToken();
					SVDBAssignStmt assign_stmt = new SVDBAssignStmt();
					assign_stmt.setLHS(lvalue);
					assign_stmt.setOp(op);
					
					if (fLexer.peekOperator("#")) {
						assign_stmt.setDelayExpr(fParsers.exprParser().delay_expr());
					} else if (fLexer.peekOperator("##")) {
						// Clocking drive
						assign_stmt.setDelayExpr(fParsers.exprParser().expression());
					}

					assign_stmt.setRHS(parsers().exprParser().expression());
					stmt = assign_stmt;
				} else {
					// Assume this is an expression of some sort
					debug("  Parsing expression statement starting with \"" + fLexer.peek() + "\"");
					SVDBExprStmt expr_stmt = new SVDBExprStmt(lvalue);
					stmt = expr_stmt;
				}
				
				fLexer.readOperator(";");
			}
			
		} else {
			error("Unknown statement stem: " + fLexer.peek());
		}
		
		debug("<-- [" + level + "] statement " + fLexer.peek() + 
				" @ " + fLexer.getStartLocation().getLine() + " parent=" + parent);
		
		return stmt;
	}
	
	public SVDBActionBlockStmt action_block() throws SVParseException {
		SVDBActionBlockStmt ret = new SVDBActionBlockStmt();
		if (fLexer.peekOperator(";")) {
			SVDBStmt stmt = new SVDBNullStmt();
			ret.setStmt(stmt);
		} else if (fLexer.peekKeyword("else")) {
			fLexer.eatToken();
			ret.setElseStmt(statement(false, true));
		} else {
			ret.setStmt(statement(false, true));
			if (fLexer.peekKeyword("else")) {
				fLexer.eatToken();
				ret.setElseStmt(statement(false, true));
			}
		}
		
		return ret;
	}
	
	private SVDBForStmt for_stmt(int level) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.eatToken();
		fLexer.readOperator("(");
		SVDBForStmt stmt = new SVDBForStmt();
		stmt.setLocation(start);
		if (!fLexer.peekOperator(";")) {
			SVToken first = fLexer.peekToken();
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
			
			if (fLexer.peekOperator()) {
				// If an operator, then likely not a declaration
				fLexer.ungetToken(first);
				type = null;
			}
			SVDBBlockStmt init_block = null;
			SVDBStmt init_stmt;
			while (true) {
				SVDBExpr expr = parsers().exprParser().expression();
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		}
		fLexer.readOperator(";");
		
		if (!fLexer.peekOperator(";")) {
			
			while (true) {
				SVDBExpr expr = parsers().exprParser().expression();
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		}
		fLexer.readOperator(";");
		
		if (!fLexer.peekOperator(")")) {
			while (true) {
				SVDBExpr expr = parsers().exprParser().expression();
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		}
		
		fLexer.readOperator(")");
		
		stmt.setBody(statement("for", level));
		
		return stmt;
	}
	
	private SVDBProceduralContAssignStmt procedural_cont_assign() throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		String type_s = fLexer.readKeyword("assign", "deassign", "force", "release");
		AssignType type = null;
		if (type_s.equals("assign")) {
			type = AssignType.Assign;
		} else if (type_s.equals("deassign")) {
			type = AssignType.Deassign;
		} else if (type_s.equals("force")) {
			type = AssignType.Force;
		} else if (type_s.equals("release")) {
			type = AssignType.Release;
		}
		SVDBProceduralContAssignStmt assign = new SVDBProceduralContAssignStmt(type);
		assign.setLocation(start);
		
		SVDBExpr expr = fParsers.exprParser().variable_lvalue();
		if (type == AssignType.Assign || type == AssignType.Force) {
			fLexer.readOperator("=");
			expr = new SVDBAssignExpr(expr, "=", fParsers.exprParser().expression());
		}
		assign.setExpr(expr);
		
		fLexer.readOperator(";");
		
		return assign;
	}
	
	private SVDBIfStmt parse_if_stmt() throws SVParseException {
		String if_stem = fLexer.eatToken();
		
		debug("beginning of \"if\": " + if_stem);
		
		if (!if_stem.equals("if")) {
			fLexer.readKeyword("if");
		}
		
		fLexer.readOperator("(");
		SVDBIfStmt if_stmt = new SVDBIfStmt(parsers().exprParser().expression()); 
		fLexer.readOperator(")");
		
		debug("--> parse body of if");
		SVDBStmt if_body = statement();
		debug("<-- parse body of if");
		if_stmt.setIfStmt(if_body);
		
		if (fLexer.peekKeyword("else")) {
			fLexer.eatToken();
			if_stmt.setElseStmt(statement());
		}
		return if_stmt;
	}
	
	private SVDBCaseStmt parse_case_stmt() throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		String type_s = fLexer.eatToken();
		CaseType type = null;
		
		if (type_s.equals("case")) {
			type = CaseType.Case;
		} else if (type_s.equals("casex")) {
			type = CaseType.Casex;
		} else if (type_s.equals("casez")) {
			type = CaseType.Casez;
		} else if (type_s.equals("randcase")) {
			type = CaseType.Randcase;
		}
		
		SVDBCaseStmt case_stmt = new SVDBCaseStmt(type);
		fLexer.readOperator("(");
		case_stmt.setExpr(parsers().exprParser().expression());
		fLexer.readOperator(")");
		
		if (fLexer.peekKeyword("matches", "inside")) {
			// TODO: ignore for now
			fLexer.eatToken();
		}
		
		while (fLexer.peek() != null && !fLexer.peekKeyword("endcase")) {
			SVDBCaseItem item = new SVDBCaseItem();
			// Read a series of comma-separated expressions
			if (type != CaseType.Randcase && fLexer.peekKeyword("default")) {
				item.addExpr(new SVDBLiteralExpr("default"));
				fLexer.eatToken();
			} else {
				while (fLexer.peek() != null) {
					item.addExpr(fParsers.exprParser().expression());
					if (type != CaseType.Randcase && fLexer.peekOperator(",")) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
			}
			fLexer.readOperator(":");
			item.setBody(statement());
			case_stmt.addCaseItem(item);
		}
		fLexer.readKeyword("endcase");
		return case_stmt;
	}
	
}

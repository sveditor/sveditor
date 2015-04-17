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


package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.expr.SVDBOpenRangeListExpr;
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
import net.sf.sveditor.core.db.stmt.SVDBRandseqProdStmt;
import net.sf.sveditor.core.db.stmt.SVDBRandseqStmt;
import net.sf.sveditor.core.db.stmt.SVDBRepeatStmt;
import net.sf.sveditor.core.db.stmt.SVDBReturnStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitStmt;
import net.sf.sveditor.core.db.stmt.SVDBWhileStmt;
import net.sf.sveditor.core.parser.SVLexer.Context;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVBehavioralBlockParser extends SVParserBase {
	
	public static boolean isDeclAllowed(SVDBStmt stmt) {
		return (stmt.getType() == SVDBItemType.VarDeclStmt || 
				stmt.getType() == SVDBItemType.TypedefStmt);
	}
	
	public SVBehavioralBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public boolean statement(ISVDBAddChildItem parent) throws SVParseException {
		boolean ret = false;
		Context ctxt = fLexer.getContext();

		try {
			fLexer.setContext(Context.Behavioral);
			ret = statement(parent, false, true);
		} finally {
			fLexer.setContext(ctxt);
		}
		
		return ret;
	}
	
	public boolean statement(ISVDBAddChildItem parent, boolean decl_allowed, boolean ansi_decl) throws SVParseException {
		return statement_int(parent, decl_allowed, ansi_decl, true);
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
	
	private boolean statement_int(
			ISVDBAddChildItem 	parent, 
			boolean 			decl_allowed, 
			boolean 			ansi_decl, 
			boolean 			consume_terminator) throws SVParseException {
		return statement_int(parent, decl_allowed, ansi_decl, consume_terminator, false);
	}
	
	private boolean statement_int(
			ISVDBAddChildItem 	parent, 
			boolean 			decl_allowed, 
			boolean 			ansi_decl, 
			boolean 			consume_terminator,
			boolean				could_be_case_item) throws SVParseException {
		if (fDebugEn) {
			debug("--> statement tok=" + fLexer.peek() + " is_kw=" + fLexer.isKeyword() +
					" @ " + SVDBLocation.toString(fLexer.getStartLocation()) + " decl_allowed=" + decl_allowed);
		}
		Set<String> decl_keywords = (ansi_decl)?fDeclKeywordsANSI:fDeclKeywordsNonANSI;
		long start = fLexer.getStartLocation();
		
		// Try for a declaration here
		if (decl_allowed &&
				(fLexer.peekKeyword(decl_keywords) || fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypes) ||
				fLexer.isIdentifier() || fLexer.peekKeyword(
						"parameter", "localparam", "typedef","struct","union","enum","virtual"))) {
//			boolean builtin_type = fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypes);

			if (fDebugEn) {debug(" -- possible variable declaration " + fLexer.peek());}

			if (fLexer.peekKeyword(decl_keywords) || fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypes) ||
					fLexer.peekKeyword("typedef","struct","union","enum","virtual")) {
				// Definitely a declaration
				if (fDebugEn) {debug(" -- variable declaration 1 " + fLexer.peek());}
				if (!decl_allowed) {
					error("declaration in a post-declaration location");
				}
				parsers().blockItemDeclParser().parse(parent, null, start, consume_terminator);
				return decl_allowed;
			} else if (fLexer.peekKeyword("parameter", "localparam")) {
				if (!decl_allowed) {
					error("declaration in a post-declaration location");
				}
				parsers().modIfcBodyItemParser().parse_parameter_decl(parent);

				return decl_allowed;
			} else {
				// May be a declaration. Let's see
				// pkg::cls #(P)::field = 2; 
				// pkg::cls #(P)::type var;
				// field.foo
				SVToken tok = fLexer.consumeToken();

				if (fDebugEn) {debug(" -- variable declaration 2 " + fLexer.peek());}

				if (fLexer.peekOperator("::","#", "##", "[") || fLexer.peekId()) {
					boolean retry_as_statement = false;
					// Likely to be a declaration. Let's read a type
					fLexer.ungetToken(tok);
					final List<SVToken> tok_l = new ArrayList<SVToken>();
					ISVTokenListener l = new ISVTokenListener() {
						public void tokenConsumed(SVToken tok) {
							tok_l.add(tok);
						}
						public void ungetToken(SVToken tok) {
							tok_l.remove(tok_l.size()-1);
						}
					}; 
					SVDBTypeInfo type = null;
					try {
						fLexer.addTokenListener(l);
						disableErrors(true);
						type = parsers().dataTypeParser().data_type(0);
					} catch (SVParseException e) {
						if (fDebugEn) {debug("dataType error ; retrying as statement", e);}
						fLexer.ungetToken(tok_l);
						retry_as_statement = true;
 					} finally {
						disableErrors(false);
						fLexer.removeTokenListener(l);
					}
					
					if (fDebugEn) {debug("Post-read : " + fLexer.peek());}

					// Okay, what's next?
					if (!retry_as_statement) {
						if (fLexer.peekId()) {
							// Conclude that this is a declaration
							if (fDebugEn) {debug("Assume a declaration @ " + fLexer.peek());}
							if (!decl_allowed) {
								error("declaration in a non-declaration location");
							}

							parsers().blockItemDeclParser().parse(parent, type, start, consume_terminator);
							return decl_allowed;
						} else {
							if (fDebugEn) { debug("Assume a typed reference @ " + fLexer.peek());}
							// Else, this is probably a typed reference
							fLexer.ungetToken(tok_l);
							// Fall through
						}
					}
				} else {
					// More likely to not be a type
					if (fDebugEn) { debug("Not likely a type declaration");}
					fLexer.ungetToken(tok);
				}
			}
		}
		
		// time to move on to the body
		if (fDebugEn) {
			debug("non-declaration statement: " + fLexer.peek());
		}
		decl_allowed = false;

		if (fLexer.peekKeyword("begin")) {
			block_stmt(parent);
		} else if (fLexer.peekKeyword("unique","unique0","priority")) {
			// TODO: ignore unique_priority for now
			fLexer.eatToken();
			// 'if' or 'case'
			statement(parent);
		} else if (fLexer.peekKeyword("if")) {
			parse_if_stmt(parent);
		} else if (fLexer.peekKeyword("while")) {
			SVDBWhileStmt while_stmt = new SVDBWhileStmt();
			while_stmt.setLocation(start);
			fLexer.eatToken();
			fLexer.readOperator("(");
			while_stmt.setExpr(parsers().exprParser().expression());
			fLexer.readOperator(")");
			
			parent.addChildItem(while_stmt);
			
			statement(while_stmt, false,false);
		} else if (fLexer.peekKeyword("do")) {
			SVDBDoWhileStmt do_while = new SVDBDoWhileStmt();
			do_while.setLocation(start);
			fLexer.eatToken();
			parent.addChildItem(do_while);
			
			statement(do_while, false,false);
			fLexer.readKeyword("while");
			fLexer.readOperator("(");
			do_while.setCond(parsers().exprParser().expression());
			fLexer.readOperator(")");
			fLexer.readOperator(";");
		} else if (fLexer.peekKeyword("repeat")) {
			SVDBRepeatStmt repeat = new SVDBRepeatStmt();
			repeat.setLocation(start);
			fLexer.eatToken();
			fLexer.readOperator("(");
			repeat.setExpr(parsers().exprParser().expression());
			fLexer.readOperator(")");
			parent.addChildItem(repeat);
			statement_int(repeat, false, false, consume_terminator);
		} else if (fLexer.peekKeyword("forever")) {
			SVDBForeverStmt forever = new SVDBForeverStmt();
			forever.setLocation(start);
			fLexer.eatToken();
			parent.addChildItem(forever);
			statement_int(forever, false,false, consume_terminator);
		} else if (fLexer.peekKeyword("for")) {
			for_stmt(parent);
		} else if (fLexer.peekKeyword("foreach")) {
			SVDBForeachStmt foreach = new SVDBForeachStmt();
			foreach.setLocation(start);
			fLexer.eatToken();
			fLexer.readOperator("(");
			foreach.setCond(parsers().exprParser().foreach_loopvar());
			fLexer.readOperator(")");
			parent.addChildItem(foreach);
			statement_int(foreach, false,false, consume_terminator);
		} else if (fLexer.peekKeyword("fork")) {
			SVDBForkStmt fork = new SVDBForkStmt();
			fork.setLocation(start);
			
			parent.addChildItem(fork);
			decl_allowed = true;
			fLexer.eatToken();
			
			// Read block identifier
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			
			while (fLexer.peek() != null && 
					!fLexer.peekKeyword("join", "join_none", "join_any")) {
				if (fDebugEn) {
					debug("--> Fork Statement");
				}
				// Allow declarations at the root of the fork
				decl_allowed = statement_int(fork, decl_allowed, true, true);
				if (fDebugEn) {
					debug("<-- Fork Statement");
				}
			}
			fork.setEndLocation(fLexer.getStartLocation());
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
		} else if (fLexer.peekKeyword("case", "casex", "casez","randcase")) {
			parse_case_stmt(parent);
		} else if (fLexer.peekKeyword("wait")) {
			SVDBWaitStmt wait_stmt;
			fLexer.eatToken();
			
			if (fLexer.peekKeyword("fork")) {
				wait_stmt = new SVDBWaitForkStmt();
				fLexer.eatToken();
				if (consume_terminator) {
					fLexer.readOperator(";");
				}
				parent.addChildItem(wait_stmt);
			} else {
				wait_stmt = new SVDBWaitStmt();
				fLexer.readOperator("(");
				wait_stmt.setExpr(parsers().exprParser().expression());
				fLexer.readOperator(")");
				parent.addChildItem(wait_stmt);
				if (!fLexer.peekOperator(";")) {
					statement_int(wait_stmt, false,false, consume_terminator);
				} else if (consume_terminator) {
					fLexer.readOperator(";");
				}
			}
		} else if (fLexer.peekOperator("->>", "->", "-->")) {
			// TODO: preserve contents
			SVDBEventTriggerStmt event_trigger = new SVDBEventTriggerStmt();
			String tt =  fLexer.eatToken();
			
			// Non-blocking operator can have a [delay_or_event_control] module
			if (tt.equals("->>"))  {
				// repeat
				if (fLexer.peekKeyword("repeat")) {
					SVDBRepeatStmt repeat = new SVDBRepeatStmt();
					repeat.setLocation(start);
					fLexer.eatToken(); // repeat
					fLexer.readOperator("(");
					repeat.setExpr(parsers().exprParser().expression());
					fLexer.readOperator(")");
					
					fLexer.readOperator("@");
					if (fLexer.peekOperator("(")) {
						fLexer.eatToken();
						SVDBEventControlStmt event_stmt = new SVDBEventControlStmt();
						event_stmt.setExpr(fParsers.exprParser().event_expression());
						event_trigger.setDelayOrEventControl(event_stmt);
						fLexer.readOperator(")");
					} else {
						SVDBEventControlStmt event_stmt = new SVDBEventControlStmt();
						event_stmt.setExpr(fParsers.exprParser().event_expression());
						event_trigger.setDelayOrEventControl(event_stmt);
					}
				} else if (fLexer.peekOperator("@")) {
					SVDBEventControlStmt event_stmt = new SVDBEventControlStmt();
					fLexer.eatToken();
					
					if (fLexer.peekOperator("(")) {
						fLexer.eatToken();
						event_stmt.setExpr(parsers().exprParser().event_expression());
						event_trigger.setDelayOrEventControl(event_stmt);
						fLexer.readOperator(")");
					} else {
						event_stmt.setExpr(parsers().exprParser().event_expression());
						event_trigger.setDelayOrEventControl(event_stmt);
					}
				} else if (fLexer.peekOperator("#", "##")) {
					// Delay
					SVDBDelayControlStmt delay_stmt = new SVDBDelayControlStmt();
					
					delay_stmt.setExpr(fParsers.exprParser().delay_expr(3));		// uses min/typ/max
					event_trigger.setDelayOrEventControl(delay_stmt);
					// TODO: SGD - Matt, can I ask you to patch this thing	
					//	statement_int(delay_stmt, false, true, consume_terminator);
				}
			}
			
			
			event_trigger.setHierarchicalEventIdentifier(parsers().exprParser().expression());
			if (consume_terminator) {
				fLexer.readOperator(";");
			}
			parent.addChildItem(event_trigger);
		} else if (fLexer.peekOperator("@")) {
			SVDBEventControlStmt event_stmt = new SVDBEventControlStmt();
//			fLexer.eatToken();
//			event_stmt.setExpr(parsers().exprParser().event_expression());
			event_stmt.setExpr(parsers().exprParser().clocking_event());
			parent.addChildItem(event_stmt);

			// statement_or_null
			statement_int(event_stmt, decl_allowed, ansi_decl, consume_terminator);
		} else if (fLexer.peekOperator("#", "##")) {
			SVDBDelayControlStmt delay_stmt = new SVDBDelayControlStmt();
			
			delay_stmt.setExpr(fParsers.exprParser().delay_expr(2));
			statement_int(delay_stmt, false, true, consume_terminator);
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
			
			if (consume_terminator) {
				fLexer.readOperator(";");
			}
			parent.addChildItem(disable_stmt);
		} else if (fLexer.peekKeyword("end")) {
			// An unmatched 'end' signals that we're missing some
			// behavioral construct
			error("Unexpected 'end' without matching 'begin'");
		} else if (fLexer.peekKeyword("assert","assume","cover", "expect")) {
			parsers().assertionParser().parse(parent, "");
		} else if (fLexer.peekKeyword("return")) {
			if (fDebugEn) {
				debug("return statement");
			}
			SVDBReturnStmt return_stmt = new SVDBReturnStmt();
			return_stmt.setLocation(fLexer.getStartLocation());
			
			fLexer.eatToken();
			if (!fLexer.peekOperator(";")) {
				return_stmt.setExpr(parsers().exprParser().expression());
			}
			if (consume_terminator) {
				fLexer.readOperator(";");
			}
			parent.addChildItem(return_stmt);
		} else if (fLexer.peekKeyword("break")) {
			SVDBBreakStmt break_stmt = new SVDBBreakStmt();
			break_stmt.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
			if (consume_terminator) {
				fLexer.readOperator(";");
			}
			parent.addChildItem(break_stmt);
		} else if (fLexer.peekKeyword("continue")) {
			SVDBContinueStmt continue_stmt = new SVDBContinueStmt();
			continue_stmt.setLocation(start);
			fLexer.eatToken();
			if (consume_terminator) {
				fLexer.readOperator(";");
			}
			parent.addChildItem(continue_stmt);
		} else if (fLexer.peekKeyword("assign", "deassign", "force", "release")) {
			procedural_cont_assign(parent);
		} else if (SVParser.isFirstLevelScope(fLexer.peek(), 0) ||
			SVParser.isSecondLevelScope(fLexer.peek())) {
			error("Unexpected non-behavioral statement keyword " + fLexer.peek());
		} else if (fLexer.peekOperator(";")) {
			SVDBNullStmt null_stmt = new SVDBNullStmt();
			null_stmt.setLocation(start);
			fLexer.eatToken();
			parent.addChildItem(null_stmt);
		} else if (fLexer.peekId() || 
				fLexer.peekKeyword(SVKeywords.fBuiltinTypes) ||
				fLexer.peekKeyword("this", "super") || 
				fLexer.peekOperator()) {
			if (fDebugEn) { debug("non-kw statement: " + fLexer.peek());}
			SVToken id = fLexer.consumeToken();
			
			if (fLexer.peekOperator(":")) {
				// Labeled statement
				if (!could_be_case_item) {
					String label = id.getImage();
					fLexer.eatToken();
					SVDBLabeledStmt l_stmt = new SVDBLabeledStmt();
					l_stmt.setLocation(start);
					l_stmt.setLabel(label);
					parent.addChildItem(l_stmt);
					statement(l_stmt, decl_allowed, ansi_decl);
				}
			} else {
				fLexer.ungetToken(id);

				expression_stmt(start, parent, null, consume_terminator);
			}
		} else if (fLexer.peekKeyword("randsequence")) {
			error("randsequence unsupported");
//			randsequence_stmt(parent);
		} else {
			error("Unknown statement stem: " + fLexer.peek());
		}
		
		if (fDebugEn) {
			debug("<-- statement " + fLexer.peek() + 
					" @ " + SVDBLocation.unpackLineno(fLexer.getStartLocation()) + " " + decl_allowed);
		}
		return decl_allowed;
	}
	
	/*
	private SVDBExpr convertTypeInfoToLVal(SVDBTypeInfo info) throws SVParseException {
		if (info instanceof SVDBTypeInfoUserDef) {
			SVDBTypeInfoUserDef ud = (SVDBTypeInfoUserDef)info;
			if (ud.getParameters() != null && ud.getParameters().getParameters().size() > 0) {
				SVDBParamIdExpr p_id = new SVDBParamIdExpr(ud.getName());
				for (SVDBParamValueAssign pa : ud.getParameters().getParameters()) {
					p_id.addParamExpr(pa.getValue());
				}
				return p_id;
			} else {
				return new SVDBIdentifierExpr(ud.getName());
			}
		} else {
			error("Expecting user-defined type");
			return new SVDBIdentifierExpr(info.getName());
		}
	}
	 */
	
	private void expression_stmt(long start, ISVDBAddChildItem parent, SVDBExpr lvalue, boolean consume_terminator) throws SVParseException {
		if (fDebugEn) {	
			debug("--> expression_stmt: " + fLexer.peek());
		}
		
		if (lvalue == null) {
			lvalue = fParsers.exprParser().variable_lvalue();
		}

		// If an assignment
		if (fLexer.peekOperator(SVOperators.fAssignmentOps)) {
			String op = fLexer.eatToken();
			SVDBAssignStmt assign_stmt = new SVDBAssignStmt();
			assign_stmt.setLocation(start);
			assign_stmt.setLHS(lvalue);
			assign_stmt.setOp(op);
			
			if (fLexer.peekOperator("#", "##")) {
				assign_stmt.setDelayExpr(fParsers.exprParser().delay_expr(2));
			} else if (fLexer.peekOperator("@")) {
				assign_stmt.setDelayExpr(fParsers.exprParser().clocking_event());
			} else if (fLexer.peekOperator("##")) {
				// Clocking drive
				assign_stmt.setDelayExpr(fParsers.exprParser().expression());
			}

			assign_stmt.setRHS(parsers().exprParser().expression());
			parent.addChildItem(assign_stmt);
		} else {
			// Assume this is an expression of some sort
			if (fDebugEn) {
				debug("  Parsing expression statement starting with \"" + fLexer.peek() + "\"");
			}
			SVDBExprStmt expr_stmt = new SVDBExprStmt(lvalue);
			expr_stmt.setLocation(start);
			parent.addChildItem(expr_stmt);
		}
		
		if (consume_terminator) {
			fLexer.readOperator(";");
		}
		
		if (fDebugEn) {
			debug("<-- expression_stmt: " + fLexer.peek());
		}

	}
	
	public void action_block(SVDBActionBlockStmt parent) throws SVParseException {
		if (fLexer.peekOperator(";")) {
			long start = fLexer.getStartLocation();
			fLexer.eatToken();
			SVDBStmt stmt = new SVDBNullStmt();
			stmt.setLocation(start);
			parent.addChildItem(stmt);
		} else if (fLexer.peekKeyword("else")) {
			fLexer.eatToken();
			statement_int(parent, false, true, true);
		} else {
			statement_int(parent, false, true, true);

			if (fLexer.peekKeyword("else")) {
				fLexer.eatToken();
				statement_int(parent, false, true, true);
			}
		}
	}
	
	public void action_block_stmt(SVDBActionBlockStmt parent) throws SVParseException {
		if (fLexer.peekOperator(";")) {
			long start = fLexer.getStartLocation();
			fLexer.eatToken();
			SVDBStmt stmt = new SVDBNullStmt();
			stmt.setLocation(start);
			parent.addChildItem(stmt);
		} else {
			// Check for begin / end
			if (fLexer.peekKeyword("begin"))  {
				fLexer.eatToken();
				while (!fLexer.peekKeyword("end"))  {
					statement_int(parent, false, true, true);
				}
				fLexer.readKeyword("end");
			}
			else  {
				fLexer.eatToken();
				// Check for hierarchy token and eat it if exists
				if (fLexer.peekOperator("."))  {
					fLexer.eatToken();
				}
				statement_int(parent, false, true, true);
			}
		}
	}
	
	private SVDBForStmt for_stmt(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		fLexer.eatToken();
		fLexer.readOperator("(");
		SVDBForStmt for_stmt = new SVDBForStmt();
		for_stmt.setLocation(start);
		if (fLexer.peek() != null && !fLexer.peekOperator(";")) {
			SVDBBlockStmt init_stmt = new SVDBBlockStmt();
			
			statement_int(init_stmt, true, true, false);
			
			while (fLexer.peekOperator(",")) {
				fLexer.readOperator(",");
				statement_int(init_stmt, true, true, false);
			}
		}
		fLexer.readOperator(";");
		
		if (!fLexer.peekOperator(";")) {
			SVDBBlockStmt cond_stmt = new SVDBBlockStmt();
			for_stmt.setTestStmt(cond_stmt);
			
			while (fLexer.peek() != null) {
				SVDBExprStmt expr_stmt = new SVDBExprStmt();
				expr_stmt.setLocation(fLexer.getStartLocation());
				SVDBExpr expr = fParsers.exprParser().expression();
				expr_stmt.setExpr(expr);
				cond_stmt.addChildItem(expr_stmt);

				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		}
		fLexer.readOperator(";");
		
		if (!fLexer.peekOperator(")")) {
			SVDBBlockStmt incr_stmt = new SVDBBlockStmt();
			for_stmt.setIncrstmt(incr_stmt);
			
			while (fLexer.peek() != null) {
				SVDBExprStmt expr_stmt = new SVDBExprStmt();
				expr_stmt.setLocation(fLexer.getStartLocation());
				SVDBExpr expr = fParsers.exprParser().expression();
				expr_stmt.setExpr(expr);
				incr_stmt.addChildItem(expr_stmt);
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		}
		
		fLexer.readOperator(")");
		parent.addChildItem(for_stmt);
		
		statement(for_stmt, false,false);
		
		return for_stmt;
	}
	
	private void procedural_cont_assign(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
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
		parent.addChildItem(assign);
		
		SVDBExpr expr = fParsers.exprParser().variable_lvalue();
		if (type == AssignType.Assign || type == AssignType.Force) {
			fLexer.readOperator("=");
			expr = new SVDBAssignExpr(expr, "=", fParsers.exprParser().expression());
		}
		assign.setExpr(expr);
		
		fLexer.readOperator(";");
	}
	
	private void block_stmt(ISVDBAddChildItem parent) throws SVParseException {
		boolean decl_allowed = true;
		SVDBBlockStmt block = new SVDBBlockStmt();
		block.setLocation(fLexer.getStartLocation());
		
		parent.addChildItem(block);
		
		// Declarations are permitted at block-start
		fLexer.eatToken();
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			block.setBlockName(fLexer.readId());
		}

		try {
			while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
				decl_allowed = statement_int(block, decl_allowed, true, true);
				//			decl_allowed = isDeclAllowed((SVDBStmt)block.getItems().get(block.getItems().size()-1));
			}
		} finally {
			if (fDebugEn) {
				debug("Setting block-end: " + fLexer.getStartLocation());
			}
			block.setEndLocation(fLexer.getStartLocation());
		}
		
		fLexer.readKeyword("end");
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readId();
		}
	}
	
	private void parse_if_stmt(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		String if_stem = fLexer.eatToken();
		
		if (fDebugEn) {
			debug("beginning of \"if\": " + if_stem);
		}
		
		if (!if_stem.equals("if")) {
			fLexer.readKeyword("if");
		}
		
		fLexer.readOperator("(");
		SVDBIfStmt if_stmt = new SVDBIfStmt(parsers().exprParser().expression()); 
		fLexer.readOperator(")");
		if_stmt.setLocation(start);
		parent.addChildItem(if_stmt);
		
		if (fDebugEn) {
			debug("--> parse body of if");
		}
		statement(if_stmt);
		if (fDebugEn) {
			debug("<-- parse body of if");
		}
		
		if (fLexer.peekKeyword("else")) {
			fLexer.eatToken();
			statement(if_stmt);
		}
	}
	
	private void parse_case_stmt(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		String type_s = fLexer.eatToken();
		CaseType type = null;
//		List<SVToken> token_l = new ArrayList<SVToken>();
		boolean case_inside = false;
		
		if (type_s.equals("case")) {
			type = CaseType.Case;
		} else if (type_s.equals("casex")) {
			type = CaseType.Casex;
		} else if (type_s.equals("casez")) {
			type = CaseType.Casez;
		} else if (type_s.equals("randcase")) {
			type = CaseType.Randcase;
		}
		
		// NOTE: randcase doesn't have a switch expression
		SVDBCaseStmt case_stmt = new SVDBCaseStmt(type);
		case_stmt.setLocation(start);
		if (!type_s.equals("randcase")) {
			fLexer.readOperator("(");
			case_stmt.setExpr(parsers().exprParser().expression());
			fLexer.readOperator(")");
		}
		parent.addChildItem(case_stmt);

		if (fLexer.peekKeyword("matches", "inside")) {
			// TODO: ignore for now
			String casetype = fLexer.eatToken();
			
			if (casetype.equals("inside")) {
				case_inside = true;
			}
		}
		
		while (fLexer.peek() != null && !fLexer.peekKeyword("endcase")) {
			SVDBCaseItem item = new SVDBCaseItem();
			// Read a series of comma-separated expressions
			if (type != CaseType.Randcase && fLexer.peekKeyword("default")) {
				item.addExpr(new SVDBLiteralExpr("default"));
				fLexer.eatToken();
				// Default has an optional : after it
				if (fLexer.peekOperator(":"))  {
					fLexer.readOperator(":");
				}
			} else {
				while (fLexer.peek() != null) {
					if (case_inside) {
						SVDBOpenRangeListExpr range_list = new SVDBOpenRangeListExpr();
						fParsers.exprParser().open_range_list_1(range_list.getRangeList());
						item.addExpr(range_list);
					} else {
						item.addExpr(fParsers.exprParser().expression());
					}
					if (type != CaseType.Randcase && fLexer.peekOperator(",")) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
				fLexer.readOperator(":");
			}
			
			// Peek ahead to see whether we have a body
			if (fDebugEn) {
				debug("  post-':' -- " + fLexer.peek());
			}
			
			if (fLexer.peekId() || fLexer.peekNumber() || 
					fLexer.peekOperator("{", "(", "+", "-")) {
				SVDBBlockStmt null_block = new SVDBBlockStmt();
				SVCapturingTokenListener tl = new SVCapturingTokenListener();
				fLexer.addTokenListener(tl);
				
				try {
					// Read an statement
					if (fLexer.peekNumber()) {
						fParsers.exprParser().expression();
					} else {
						statement_int(null_block, false, true, true, true);
					}
				} catch (SVParseException e) {
					// Ignore parse error (if any)
				} finally {
					fLexer.removeTokenListener(tl);
				}

				if (fDebugEn) {
					debug("  post speculative-expression parse: " + fLexer.peek());
				}
				if (fLexer.peekOperator(",", ":")) {
					// Null statement
				
					fLexer.ungetToken(tl.getTokenList());
				} else {
					// Non-null statement
					fLexer.ungetToken(tl.getTokenList());
					if (fDebugEn) {
						debug("  post-unget: " + fLexer.peek());
					}
					statement(item);
				}
			} else if (!fLexer.peekKeyword("endcase")) {
				statement(item);
			}
		
			case_stmt.addCaseItem(item);
		}
		fLexer.readKeyword("endcase");
	}
	
	private void randsequence_stmt(ISVDBAddChildItem parent) throws SVParseException {
		SVDBRandseqStmt stmt = new SVDBRandseqStmt();
		stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("randsequence");
		
		fLexer.readOperator("(");
		if (fLexer.peekId()) {
			stmt.setName(fLexer.readId());
		}
		fLexer.readOperator(")");
		
		while (fLexer.peek() != null && !fLexer.peekKeyword("endsequence")) {
			randsequence_production(stmt);
			
		}
	}
	
	private void randsequence_production(SVDBRandseqStmt rs) throws SVParseException {
		SVDBRandseqProdStmt stmt = new SVDBRandseqProdStmt();
		stmt.setLocation(fLexer.getStartLocation());
		
		SVDBTypeInfo type = fParsers.dataTypeParser().data_type(0);
		
		if (fLexer.peekOperator("(", ":")) {
			// The production identifier was provided, not the datatype
			stmt.setName(type.getName());
		} else {
			stmt.setRetType(type);
			stmt.setName(fLexer.readId());
		}
	
		if (fLexer.peekKeyword("(")) {
			// tf_port_list
		}
		
		// rs_rule { | rs_rule }
		// rs_rule ::= rs_production_list [ := weight_specification [rs_code_block]]
		// rs_production_list 

		while (fLexer.peek() != null) {
			if (fLexer.peekKeyword("rand")) {
				fLexer.readKeyword("rand");
				fLexer.readKeyword("join");
				if (fLexer.peekOperator("(")) {
					fLexer.eatToken();
					SVDBExpr expr = fParsers.exprParser().expression();
					fLexer.readOperator(")");
					
					// production_item
					String production_id = fLexer.readId();
				
					if (fLexer.peekOperator("(")) {
						fLexer.eatToken();
						// list_of_arguments
						fLexer.readOperator(")");
					}
					
				}
			} else {
				// rs_prod {rs_prod}
			}
		}
		
		fLexer.readKeyword(":");
		
	}
	
}

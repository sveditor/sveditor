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
import java.util.Set;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.expr.SVLiteralExpr;
import net.sf.sveditor.core.db.stmt.SVDBActionBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBCaseItem;
import net.sf.sveditor.core.db.stmt.SVDBCaseStmt;
import net.sf.sveditor.core.db.stmt.SVDBDisableStmt;
import net.sf.sveditor.core.db.stmt.SVDBDoWhileStmt;
import net.sf.sveditor.core.db.stmt.SVDBEventControlStmt;
import net.sf.sveditor.core.db.stmt.SVDBEventTriggerStmt;
import net.sf.sveditor.core.db.stmt.SVDBForStmt;
import net.sf.sveditor.core.db.stmt.SVDBForeachStmt;
import net.sf.sveditor.core.db.stmt.SVDBForeverStmt;
import net.sf.sveditor.core.db.stmt.SVDBForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBForkStmt.JoinType;
import net.sf.sveditor.core.db.stmt.SVDBIfStmt;
import net.sf.sveditor.core.db.stmt.SVDBRepeatStmt;
import net.sf.sveditor.core.db.stmt.SVDBReturnStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitStmt;
import net.sf.sveditor.core.db.stmt.SVDBWhileStmt;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVBehavioralBlockParser extends SVParserBase {
	private static SVDBStmt				fSpecialNonNull;
	private static final Set<String>	fIfStems;
	
	static {
		fSpecialNonNull = new SVDBVarDeclStmt(null, 0);
		fSpecialNonNull.setLocation(new SVDBLocation(-1, -1));
		
		fIfStems = new HashSet<String>();
		fIfStems.add("if");
		fIfStems.add("unique");
		fIfStems.add("unique0");
		fIfStems.add("priority");
	}
	
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
				lexer().peek() + " @ " + lexer().getStartLocation().getLine());
		SVDBStmt stmt = null;
		Set<String> decl_keywords = (ansi_decl)?fDeclKeywordsANSI:fDeclKeywordsNonANSI;
		
		if (decl_allowed) {
			SVToken id = null;
			
			// Try for a declaration here
			if (lexer().peekKeyword(decl_keywords) || 
					(lexer().peekKeyword(SVKeywords.fBuiltinTypes) && !lexer().peekKeyword("void")) ||
					lexer().isIdentifier()) {
				
				// Variable declarations
				id = lexer().consumeToken(); // should be beginning of type declaration
				
				if ((lexer().peekKeyword() && !lexer().peekKeyword(fDeclKeywordsNonANSI)) ||
						(lexer().peekOperator() && !lexer().peekOperator("#", "["))) {
					// likely a statement
					lexer().ungetToken(id);
				} else {
					debug("Pre-var parse: " + id.getImage());
					SVDBStmt decl = parsers().blockItemDeclParser().parse();
					if (decl.getType() == SVDBItemType.VarDeclStmt) {
						debug("Result is " + ((SVDBVarDeclStmt)decl).getVarList().size() + " vars");
					} else if (decl.getType() == SVDBItemType.TypedefStmt) {
//						debug("Result is " + ((SVDBTypedefStmt)decl).getgetVarList().size() + " vars");
					}
					
					// Bail for now
					return decl; 
				}
			} else if (lexer().peekKeyword("typedef")) {
				// TODO: permit local type declaration
//				break;
			} else {
				
				// time to move on to the body
				debug("non-declaration statement: " + lexer().peek());
			}
		}
		
		if (lexer().peekKeyword("begin")) {
			SVDBBlockStmt block = new SVDBBlockStmt();
			// Declarations are permitted at block-start
			decl_allowed = true;
			lexer().eatToken();
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
			while (lexer().peek() != null && !lexer().peekKeyword("end")) {
				SVDBStmt tmp = statement(decl_allowed, true, parent, level+1);
				decl_allowed = (tmp.getType() == SVDBItemType.VarDeclStmt);
				block.addStmt(tmp);
			}
			lexer().readKeyword("end");
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
			stmt = block;
		} else if (lexer().peekKeyword(fIfStems)) {
			String if_stem = lexer().eatToken();
			
			debug("beginning of \"if\": " + if_stem);
			
			if (!if_stem.equals("if")) {
				lexer().readKeyword("if");
			}
			
			lexer().readOperator("(");
			SVDBIfStmt if_stmt = new SVDBIfStmt(parsers().exprParser().expression()); 
			lexer().readOperator(")");
			
			debug("--> parse body of if");
			SVDBStmt if_body = statement(false, true, "if", level);
			debug("<-- parse body of if");
			if_stmt.setIfStmt(if_body);
			
			if (lexer().peekKeyword("else")) {
				lexer().eatToken();
				if_stmt.setElseStmt(statement("else", level));
			}
			stmt = if_stmt;
		} else if (lexer().peekKeyword("while")) {
			lexer().eatToken();
			lexer().readOperator("(");
			SVDBWhileStmt while_stmt = new SVDBWhileStmt(parsers().exprParser().expression());
			lexer().readOperator(")");
			
			while_stmt.setBody(statement("while", level));
			stmt = while_stmt;
		} else if (lexer().peekKeyword("do")) {
			SVDBDoWhileStmt do_while = new SVDBDoWhileStmt();
			lexer().eatToken();
			do_while.setBody(statement("do", level));
			lexer().readKeyword("while");
			lexer().readOperator("(");
			do_while.setCond(parsers().exprParser().expression());
			lexer().readOperator(")");
			lexer().readOperator(";");
			stmt = do_while;
		} else if (lexer().peekKeyword("repeat")) {
			SVDBRepeatStmt repeat = new SVDBRepeatStmt();
			lexer().eatToken();
			lexer().readOperator("(");
			repeat.setExpr(parsers().exprParser().expression(false));
			lexer().readOperator(")");
			repeat.setBody(statement("repeat", level));
			stmt = repeat;
		} else if (lexer().peekKeyword("forever")) {
			lexer().eatToken();
			SVDBForeverStmt forever = new SVDBForeverStmt();
			forever.setBody(statement("forever", level));
			stmt = forever;
		} else if (lexer().peekKeyword("for")) {
			stmt = for_stmt(level);
		} else if (lexer().peekKeyword("foreach")) {
			SVDBForeachStmt foreach = new SVDBForeachStmt();
			lexer().eatToken();
			lexer().readOperator("(");
			foreach.setCond(parsers().exprParser().expression());
			lexer().readOperator(")");
			foreach.setBody(statement("foreach", level));
			
			stmt = foreach;
		} else if (lexer().peekKeyword("fork")) {
			SVDBForkStmt fork = new SVDBForkStmt();
			lexer().eatToken();
			
			// Read block identifier
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
			
			while (lexer().peek() != null && 
					!lexer().peekKeyword("join", "join_none", "join_any")) {
				debug("--> Fork Statement");
				fork.addStmt(statement("fork", level));
				debug("<-- Fork Statement");
			}
			// Read join
			String join_type = lexer().readKeyword("join", "join_none", "join_any");
			if (join_type.equals("join")) {
				fork.setJoinType(JoinType.Join);
			} else if (join_type.equals("join_none")) {
				fork.setJoinType(JoinType.JoinNone);
			} else if (join_type.equals("join_any")) {
				fork.setJoinType(JoinType.JoinAny);
			}
			stmt = fork;
		} else if (lexer().peekKeyword("case", "casex", "casez")) {
			SVDBCaseStmt case_stmt = new SVDBCaseStmt();
			lexer().eatToken();
			lexer().readOperator("(");
			case_stmt.setExpr(parsers().exprParser().expression());
			lexer().readOperator(")");
			
			while (lexer().peek() != null && !lexer().peekKeyword("endcase")) {
				SVDBCaseItem item = new SVDBCaseItem();
				// Read a series of comma-separated expressions
				if (lexer().peekKeyword("default")) {
					item.addExpr(new SVLiteralExpr("default"));
					lexer().eatToken();
				} else {
					while (lexer().peek() != null) {
						item.addExpr(parsers().exprParser().expression(false));
						if (!lexer().peekOperator(",")) {
							break;
						} else {
							lexer().eatToken();
						}
					}
				}
				lexer().readOperator(":");
				item.setBody(statement("case", level));
				case_stmt.addCaseItem(item);
			}
			lexer().readKeyword("endcase");
			stmt = case_stmt;
		} else if (lexer().peekKeyword("wait")) {
			SVDBWaitStmt wait_stmt = new SVDBWaitStmt();
			lexer().eatToken();
			
			if (lexer().peekKeyword("fork")) {
				wait_stmt.setType(SVDBItemType.WaitForkStmt);
				lexer().eatToken();
				lexer().readOperator(";");
			} else {
				lexer().readOperator("(");
				wait_stmt.setExpr(parsers().exprParser().expression());
				lexer().readOperator(")");
				if (!lexer().peekOperator(";")) {
					wait_stmt.setStmt(statement("wait", level));
				} else {
					lexer().readOperator(";");
				}
			}
			stmt = wait_stmt;
		} else if (lexer().peekOperator("->", "->>")) {
			SVDBEventTriggerStmt event_trigger = new SVDBEventTriggerStmt();
			String tt = lexer().eatToken();
			
			// TODO: handle [delay_or_event_control] after ->>
			
			event_trigger.setHierarchicalEventIdentifier(parsers().exprParser().expression());
			stmt = event_trigger;
			lexer().readOperator(";");
			stmt = event_trigger;
		} else if (lexer().peekOperator("@")) {
			SVDBEventControlStmt event_stmt = new SVDBEventControlStmt();
			lexer().eatToken();
			event_stmt.setExpr(parsers().exprParser().event_expression());
			
			stmt = event_stmt;
		} else if (lexer().peekKeyword("disable")) {
			SVDBDisableStmt disable_stmt = new SVDBDisableStmt();
			lexer().eatToken();
			if (lexer().peekKeyword("fork")) {
				lexer().eatToken();
				disable_stmt.setType(SVDBItemType.DisableForkStmt);
			} else {
				disable_stmt.setHierarchicalId(parsers().exprParser().expression());
			}
			
			lexer().readOperator(";");
			stmt = disable_stmt;
		} else if (lexer().peekKeyword("end")) {
			// An unmatched 'end' signals that we're missing some
			// behavioral construct
			error("Unexpected 'end' without matching 'begin' in level " + parent);
		} else if (lexer().peekKeyword("assert")) {
			stmt = parsers().assertionParser().parse();
		} else if (lexer().peekKeyword("return")) {
			SVDBReturnStmt return_stmt = new SVDBReturnStmt();
			
			debug("return statement");
			
			lexer().eatToken();
			if (!lexer().peekOperator(";")) {
				return_stmt.setExpr(parsers().exprParser().expression());
			}
			lexer().readOperator(";");
			stmt = return_stmt;
		} else if (lexer().peekKeyword("break")) {
			SVDBStmt break_stmt = new SVDBStmt(SVDBItemType.BreakStmt);
			lexer().eatToken();
			lexer().readOperator(";");
			stmt = break_stmt;
		} else if (lexer().peekKeyword("continue")) {
			SVDBStmt continue_stmt = new SVDBStmt(SVDBItemType.ContinueStmt);
			lexer().eatToken();
			lexer().readOperator(";");
			stmt = continue_stmt;
		} else if (ParserSVDBFileFactory.isFirstLevelScope(lexer().peek(), 0) ||
			ParserSVDBFileFactory.isSecondLevelScope(lexer().peek())) {
			error("Unexpected non-behavioral statement keyword " + lexer().peek());
		} else if (lexer().peekOperator(";")) {
			stmt = new SVDBStmt(SVDBItemType.NullStmt);
			lexer().eatToken();
		} else if (lexer().peekId() || 
				lexer().peekKeyword(SVKeywords.fBuiltinTypes) ||
				lexer().peekKeyword("this", "super") || 
				lexer().peekOperator()) {
			boolean taken = false;
			SVToken id = lexer().consumeToken();
			
			// TODO: Careful. We should never be entering on ':' as far as I know
			if (lexer().peekOperator(":")) {
				if (lexer().peekOperator(":")) {
					debug("  likely assertion @ " + lexer().getStartLocation().getLine());
					lexer().eatToken();
					if (lexer().peekKeyword("assert")) {
						taken = true;
						stmt = parsers().assertionParser().parse();
					}
					// likely an assertion
				}
			} else {
				lexer().ungetToken(id);
				
				
				// Assume this is an expression of some sort
				debug("  Parsing expression statement starting with \"" + lexer().peek() + "\"");
				parsers().exprParser().expression();
				lexer().readOperator(";");
				stmt = fSpecialNonNull;
			}
			
			/*
			if (!taken) {
				if (lexer().peekOperator()) {
					error("Unknown operator \"" + lexer().peek() + "\"");
				}
				
				// Scan to a semi-colon boundary
				while (lexer().peek() != null && !lexer().peekOperator(";")) {
					// Since we're scanning, keep a look out for upper-level scope
					// 
					if (ParserSVDBFileFactory.isFirstLevelScope(lexer().peek(), 0) ||
							ParserSVDBFileFactory.isSecondLevelScope(lexer().peek())) {
							error("Unexpected non-behavioral statement keyword " + lexer().peek());
					}
					lexer().eatToken();
				}
				lexer().readOperator(";");
			}
			 */
		} else {
			error("Unknown statement stem: " + lexer().peek());
		}
		
		debug("<-- [" + level + "] statement " + lexer().peek() + 
				" @ " + lexer().getStartLocation().getLine() + " parent=" + parent);
		
		return stmt;
	}
	
	public SVDBActionBlockStmt action_block() throws SVParseException {
		SVDBActionBlockStmt ret = new SVDBActionBlockStmt();
		if (lexer().peekOperator(";")) {
			SVDBStmt stmt = new SVDBStmt(SVDBItemType.NullStmt);
			ret.setStmt(stmt);
		} else if (lexer().peekKeyword("else")) {
			lexer().eatToken();
			ret.setElseStmt(statement(false, true));
		} else {
			ret.setStmt(statement(false, true));
			if (lexer().peekKeyword("else")) {
				lexer().eatToken();
				ret.setElseStmt(statement(false, true));
			}
		}
		
		return ret;
	}
	
	private SVDBForStmt for_stmt(int level) throws SVParseException {
		SVDBLocation start = lexer().getStartLocation();
		lexer().eatToken();
		lexer().readOperator("(");
		SVDBForStmt stmt = new SVDBForStmt();
		stmt.setLocation(start);
		if (!lexer().peekOperator(";")) {
			SVToken first = lexer().peekToken();
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
			
			if (lexer().peekOperator()) {
				// If an operator, then likely not a declaration
				lexer().ungetToken(first);
				type = null;
			}
			SVDBBlockStmt init_block = null;
			SVDBStmt init_stmt;
			while (true) {
				SVExpr expr = parsers().exprParser().expression();
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		}
		lexer().readOperator(";");
		
		if (!lexer().peekOperator(";")) {
			
			while (true) {
				SVExpr expr = parsers().exprParser().expression();
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		}
		lexer().readOperator(";");
		
		if (!lexer().peekOperator(")")) {
			while (true) {
				SVExpr expr = parsers().exprParser().expression();
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		}
		
		lexer().readOperator(")");
		
		stmt.setBody(statement("for", level));
		
		return stmt;
	}

}

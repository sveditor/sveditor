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


package net.sf.sveditor.core.indent;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDefaultIndenter2 implements ISVIndenter {
	private ISVIndentScanner				fScanner;
	private Stack<Tuple<String, Boolean>>	fIndentStack;
	private List<SVIndentToken>				fTokenList;
	private SVIndentToken					fCurrent;
	private String							fCurrentIndent;
	private LogHandle						fLog;
	private int								fQualifiers;
	private static final boolean			fDebugEn = false;
	private int								fNLeftParen, fNRightParen;
	private String							fIndentIncr = "\t";
	
	private int								fAdaptiveIndentEnd;
	private boolean							fTestMode;

	
	static private Map<String, Integer>		fQualifierMap;
	static private Set<String>				fPreProcDirectives;
	
	private class IndentEOFException extends RuntimeException {
		private static final long serialVersionUID = 1L;
	}

	static {
		fQualifierMap = new HashMap<String, Integer>();
		fQualifierMap.put("static", 	1 << 0);
		fQualifierMap.put("virtual", 	1 << 1);
		fQualifierMap.put("local",		1 << 2);
		fQualifierMap.put("protected",	1 << 3);
		fQualifierMap.put("public",		1 << 4);
		fQualifierMap.put("extern",		1 << 5);
		
		fPreProcDirectives = new HashSet<String>();
		fPreProcDirectives.add("`define");
		fPreProcDirectives.add("`undef");
		fPreProcDirectives.add("`ifdef");
		fPreProcDirectives.add("`else");
		fPreProcDirectives.add("`ifndef");
		fPreProcDirectives.add("`endif");
		fPreProcDirectives.add("`include");
		fPreProcDirectives.add("`timescale");
		fPreProcDirectives.add("`begin_keywords");
		fPreProcDirectives.add("`end_keywords");
	}
	
	public SVDefaultIndenter2() {
		fIndentStack = new Stack<Tuple<String,Boolean>>();
		fTokenList = new ArrayList<SVIndentToken>();
		fLog = LogFactory.getLogHandle("SVDefaultIndenter");
	}
	
	public void setAdaptiveIndent(boolean adaptive) {
		// fAdaptiveIndent = adaptive;
	}
	
	public void setAdaptiveIndentEnd(int lineno) {
		fAdaptiveIndentEnd = lineno;
	}
	
	@Override
	public void setTestMode(boolean tm) {
		fTestMode = tm;
	}

	public void init(ISVIndentScanner scanner) {
		fScanner = scanner;
		push_indent_stack("", true);
	}
	
	public String indent() {
		return indent(-1, -1);
	}
	
	public String indent(int start_line, int end_line) {
		StringBuilder sb = new StringBuilder();
		SVIndentToken 	tok;
		
		fNLeftParen = fNRightParen = 1;
		
		while ((tok = next()) != null) {
			
			// Scan forward until the end of the token list or until we find
			// a keyword
			try {
				do {
					if (tok.getType() == SVIndentTokenType.Identifier &&
							fQualifierMap.containsKey(tok.getImage())) {
						fQualifiers |= fQualifierMap.get(tok.getImage());
						tok = next();
					} else if (tok.isId("class") || tok.isId("module") ||
							tok.isId("interface") || tok.isId("program") ||
							tok.isId("package")) {
						tok = indent_ifc_module_class(tok.getImage());
						fQualifiers = 0;
					} else if (tok.isId("covergroup")) {
						tok = indent_covergroup();
					} else if (tok.isId("function") || tok.isId("task")) {
						tok = indent_task_function(tok.getImage());
						fQualifiers = 0;
					} else if (tok.isId("typedef")) {
						tok = indent_typedef();
						fQualifiers = 0;
					} else if (tok.isOp(";")) {
						fQualifiers = 0;
						tok = next();
					} else {
						tok = next();
					} 
				} while ((tok = current()) != null);
			} catch (IndentEOFException e) {
				// e.printStackTrace();
				break;
			} catch (RuntimeException e) {
				if (fTestMode) {
					throw e;
				}
			}
		}
		
		if (fTestMode) {
			if (fIndentStack.size() != 1) {
				throw new RuntimeException("IndentStack size is " + 
						fIndentStack.size() + " rather than 1");
			}
		}
		
		if (fDebugEn) {
			debug("Indent operation complete");
		}
		for (SVIndentToken t : fTokenList) {
			if ((t.getLineno() >= start_line || start_line == -1) &&
					(t.getLineno() <= end_line || end_line == -1)) {
				if (fDebugEn) {
					debug("tok \"" + t.getType() + "\" line=" + t.getLineno() + " image=" + t.getImage());
				}
				sb.append(t.getLeadingWS() + 
						t.getImage() +
						t.getTrailingWS() +
						((t.isEndLine())?"\n":""));
			}
		}
		
		return sb.toString();
	}

	public String getLineIndent(int lineno) {
		String ret = null;
		
		for (SVIndentToken t : fTokenList) {
			if (t.getLineno() == lineno) {
				ret = t.getLeadingWS();
				break;
			}
		}
		
		return ret;
	}

	public boolean isQualifierSet(String key) {
		return ((fQualifierMap.get(key) & fQualifiers) != 0);
	}

	private SVIndentToken indent_if(boolean is_else_if) {
		SVIndentToken tok = current();

		if (fDebugEn) {
			debug("--> indent_if() tok=" + tok.getImage());
		}

		start_of_scope(tok);
		
		tok = next_s();
		
		if (tok.isOp("(")) {
			tok = consume_expression();
		} else {
			//System.out.println("[ERROR] unsure what happened - tok=" + 
		    // tok.getImage());
			// bail out -- not sure what happened...
			return tok;
		}

		tok = indent_if_stmts(null);
		
		if (tok.isId("else")) {
			tok = next_s();
			if (tok.isId("if")) {
				tok = indent_if(true);
			} else {
				start_of_scope(tok);
				tok = indent_if_stmts(null);
			}
		}
		
		if (fDebugEn) {
			debug("<-- indent_if() tok=" + 
				((tok != null)?tok.getImage():"null"));
		}
		
		return tok;
	}
	
	private SVIndentToken indent_if_stmts(String parent) {
		SVIndentToken tok = current_s();
		
		// Indent the statement or block inside the 'if' clause.
		if (tok.isId("begin")) {
			parent = "begin";
			boolean begin_is_start_line = tok.isStartLine();
			
			if (begin_is_start_line) {
				enter_scope(tok);
			}
			
			tok = next_s();
			if (!begin_is_start_line) {
				enter_scope(tok);
			}
			
			while (tok != null) {
				if (fDebugEn) {
					debug("top of begin/end loop: " + tok.getType() + " " + tok.getImage());
				}
				if (tok.isId("end")) {
					leave_scope(tok);
					if (fDebugEn) {
						debug("Setting indent \"" + peek_indent() + "\"");
					}
					tok = next_s();
					
					tok = consume_labeled_block(tok);
					break;
				} else {
					// Indent statement. Note that we're already in the
					// scope that the statement should be in
					tok = indent_block_or_statement(parent, true);
				}
			}
		} else {
			enter_scope(tok);
			tok = indent_stmt(parent);
			leave_scope(tok);
		}
		
		return tok;
	}
	
	private SVIndentToken indent_fork() {
		SVIndentToken tok = current();
		
		enter_scope(tok);

		tok = next_s();
		enter_scope(tok);

		while (!tok.isId("join") && 
				!tok.isId("join_none") && 
				!tok.isId("join_any")) {
			
			tok = indent_stmt("fork");
		}
		leave_scope(tok);
		
		tok = next_s();
		
		return tok;
	}
	
	private SVIndentToken indent_loop_stmt() {
		SVIndentToken tok, first;
		
		tok = first = current();
		
		start_of_scope(tok);
		
		if (fDebugEn) {
			debug("--> indent_loop_stmt() tok=" + tok.getImage());
		}
		
		if (!tok.isId("do") && !tok.isId("forever")) {
			tok = next_s();
			if (tok.isOp("(")) {
				tok = consume_expression();
			} else {
				return tok;
			}
		} else {
			tok = next_s();
		}
		
		// tok = indent_block_or_statement(null, true);
		tok = indent_if_stmts(null);

		if (first.isId("do")) {
			// Just read to end of statement
			while (!tok.isOp(";")) {
				tok = next_s();
			}
			tok = next_s();
			
		}
		
		if (fDebugEn) {
			debug("<-- indent_loop_stmt() tok=" + 
				((tok != null)?tok.getImage():"null"));
		}
		
		return tok;
	}
	
	private SVIndentToken indent_typedef() {
		SVIndentToken tok = current();
		
		enter_scope(tok);
		
		if (fDebugEn) {
			debug("--> indent_typedef()");
		}
		
		tok = next_s();
		
		if (tok.isId("enum") || tok.isId("struct")) {
			while (!tok.isOp("{")) {
				tok = next_s();
			}

			enter_scope(tok);
			
			while (!tok.isOp("}")) {
				tok = next_s();
			}
			leave_scope(tok);
		}

		// read to the end of the statement
		while (!tok.isOp(";")) {
			tok = next_s();
		}
		tok = next_s();
		
		if (fDebugEn) {
			debug("<-- indent_typedef()");
		}
		
		leave_scope();
		return tok;
	}
	
	/**
	 * indent_ifc_module_class()
	 * 
	 * Indents a class, module or interface and the items
	 * within the body
	 * 
	 * @param item
	 * @return
	 */
	private SVIndentToken indent_ifc_module_class(String item) {
		SVIndentToken tok = current_s();
		
		String end = get_end_kw(item);
		if (fDebugEn) {
			debug("--> indent_ifc_module_class(" + item + ")");
		}

		start_of_scope(tok); 	// establish the indent of this scope
        // for adaptive-indent purposes

		tok = next_s();
		
		// push a new scope for ports and parameters 
		start_of_scope(tok);
		
		// Reach the end of the declaration
		while (!tok.isOp(";")) {
			tok = next_s();
		}
		leave_scope(tok); 
		
		tok = next_s();
		enter_scope(tok); // enter the body of the module
		
		fQualifiers = 0;
		
		// Now, read body items
		while (tok != null) {
			
			if (tok.isId(end)) {
				break;
			} else if (tok.getType() == SVIndentTokenType.Identifier &&
					fQualifierMap.containsKey(tok.getImage())) {
				fQualifiers |= fQualifierMap.get(tok.getImage());
				tok = next_s();
			} else if (tok.isId("function") || tok.isId("task")) {
				tok = indent_task_function(tok.getImage());
				fQualifiers = 0;
			} else if (tok.isId("class")) {
				tok = indent_ifc_module_class(tok.getImage());
				fQualifiers = 0;
			} else if (tok.isId("initial") || tok.isId("always") || 
					tok.isId("final")) {
				enter_scope(tok);
				tok = next_s();
				
				if (tok.isOp("@")) {
					tok = next_s(); // paren
					tok = consume_expression();
				}
				
				tok = indent_block_or_statement(null, false);
				fQualifiers = 0;
			} else if (tok.isId("covergroup")) {
				tok = indent_covergroup();
				fQualifiers = 0;
			} else if (tok.isId("constraint")) {
				tok = indent_constraint();
				fQualifiers = 0;
			} else if (tok.isPreProc() && tok.isStartLine()) {
				// Just read to the end of the line, since it's
				// unlikely this statement will end with a ';'
				while (!tok.isEndLine() && !tok.isOp(";")) {
					tok = next_s();
				}
				tok = next_s();
				fQualifiers = 0;
			} else {
				tok = indent_block_or_statement(item, true);
			}
		}
		
		leave_scope(tok);

		end_of_scope(tok); // restore scope previously set
		
		tok = consume_labeled_block(next_s());
		
		if (fDebugEn) {
			debug("--> indent_ifc_module_class(" + item + ") next=" + 
				((tok != null)?tok.getImage():"null"));
		}
		
		return tok;
	}

	private SVIndentToken indent_covergroup() {
		SVIndentToken tok = current_s();
		
		start_of_scope(tok);
		
		if (fDebugEn) {
			debug("--> indent_covergroup()");
		}
		
		start_of_scope(tok); // push a new scope for elements in the arg list
		// Reach the end of the declaration
		while (tok != null && !tok.isOp(";")) {
			tok = next_s();
		}
		leave_scope(); // leave arg-list scope
		
		tok = next_s();
		enter_scope(tok);
		
		// Now, read body items
		while (tok != null) {
		
			if (tok.isId("endgroup")) {
				leave_scope(tok);
				break;
			} else {
				tok = indent_covergroup_item();
			}
		}
		
		tok = next_s();
		
		if (fDebugEn) {
			debug("--> indent_covergroup() next=" +
				((tok != null)?tok.getImage():"null"));
		}
		
		return tok;
	}
	
	private SVIndentToken indent_constraint() {
		SVIndentToken tok = current_s();
		
		start_of_scope(tok);
		
		tok = next_s(); // name of constraint
		
		tok = next_s(); // Should be '{'
		
		if (!tok.isOp("{")) {
			// Not sure what happened...
			return tok;
		}
		
		tok = next_s();
		enter_scope(tok);
		
		while (!tok.isOp("}")) {
			tok = indent_constraint_stmt();
		}

		leave_scope(tok);

		tok = next_s();
		
		return tok;
	}
	
	private SVIndentToken indent_covergroup_item() {
		SVIndentToken tok = current();
		
		// Scan to the end of the statement / beginning of the block
		tok = next_s();
		start_of_scope(tok);
		enter_scope(tok);
		while (!tok.isOp(";") && !tok.isOp("{")) {
			tok = next_s();
		}
		leave_scope(tok);
		
		if (tok.isOp("{")) {
			boolean do_indent = true;
			int lb_count = 1, rb_count = 0;
			
			start_of_scope(tok);
			
			do {
				tok = next_s();
				if (do_indent) {
					enter_scope(tok);
					do_indent = false;
				}
				if (tok.isOp("{")) {
					lb_count++;
					start_of_scope(tok);
					do_indent = true;
				} else if (tok.isOp("}")) {
					rb_count++;
					leave_scope(tok);
				}
			} while (lb_count != rb_count);
		}
		
		tok = next_s();
		
		return tok;
	}

	private SVIndentToken indent_task_function(String item) {
		SVIndentToken tok = current_s();
		start_of_scope(tok);
		
		String end = get_end_kw(item);
		if (fDebugEn) {
			debug("--> indent_task_function(" + item + ")");
		}
		
		while (tok != null && !tok.isOp(";")) {
			tok = next_s();
		}
		
		// If this is an extern function or task, we're done
		if (!isQualifierSet("extern")) {
			// Ensure that any comments at the beginning of the
			// task/function are indented correctly
			enter_scope(tok);
			tok = next_s();
			
			while (tok != null) {
				if (tok.isId(end)) {
					break;
				} else {
					tok = indent_block_or_statement(item, true);
				}
			}
			leave_scope(tok);
			
			tok = consume_labeled_block(next_s());
		} else {
			leave_scope();
			tok = next_s();
		}

		if (fDebugEn) {
			debug("--> indent_task_function(" + item + ") " +
				((tok != null)?tok.getImage():"null"));
		}
		
		end_of_scope();
		
		return tok;
	}
	
	private SVIndentToken indent_block_or_statement(String parent, boolean parent_is_block) {
		SVIndentToken tok = current();
		if (fDebugEn) {
			debug("--> indent_block_or_statement() parent_is_block_stmt=" + parent_is_block + " tok=" + tok.getImage());
		}
		
		if (tok.isId("begin")) {
			parent = "begin";
			
			// Ensure that any comments at the beginning of the
			// block are indented correctly
			start_of_scope(tok);
			tok = next_s();
			enter_scope(tok);
			
			while (tok != null) {
				if (fDebugEn) {
					debug("top of begin/end loop: " + tok.getType() + " " + tok.getImage());
				}
				if (tok.isId("end")) {
					leave_scope(tok);
					if (fDebugEn) {
						debug("Setting indent \"" + peek_indent() + "\"");
					}
					tok = next_s();
					
					tok = consume_labeled_block(tok);
					break;
				} else {
					tok = indent_block_or_statement(parent, true);
				}
			}
		} else {
			if (!parent_is_block) {
				start_of_scope(tok);
				enter_scope(tok);
			}
			tok = indent_stmt(parent);
			
			if (!parent_is_block) {
				leave_scope();
			}
		}

		if (fDebugEn) {
			debug("<-- indent_block_or_statement() tok=" + 
				((tok != null)?tok.getImage():"null") + " parent=" + parent);
		}
		
		return tok;
	}
	
	private SVIndentToken indent_stmt(String parent) {
		SVIndentToken tok = current_s();
		
		if (fDebugEn) {
			debug("--> indent_stmt parent=" + parent + " tok=" + tok.getImage());
		}
		
		// Just indent the statement
		if (tok.isId("if")) {
			tok = indent_if(false);
		} else if (tok.isId("fork")) {
			tok = indent_fork();
		} else if (tok.isId("case")) {
			tok = indent_case();
		} else if (tok.isId("always")) {
			enter_scope(tok);
			if ((tok = next_s()).isOp("@")) {
				tok = next_s();
				tok = next_s(); // Should be either stmt or begin
				indent_block_or_statement(null, false);
			}
			leave_scope();
		} else if (tok.isId("typedef")) {
			tok = indent_typedef();
		} else if (tok.isId("while") || tok.isId("do") ||
				tok.isId("repeat") || tok.isId("forever") ||
				tok.isId("for") || tok.isId("foreach")) {
			tok = indent_loop_stmt();
		}
		/*
		else if (tok.isPreProc()) {
			boolean do_indent = true;
			// For now, just read the line. This could be a problem in some cases
			while (!tok.isOp(";") && !tok.isEndLine()) {
				tok = next_s();
				if (do_indent) {
					enter_scope(tok);
					do_indent = false;
				}
			}
			leave_scope();
			tok = next_s();
		}  */
		else {
			boolean do_next = true;
			while (!tok.isOp(";")) {
				if (parent != null) {
					if ((parent.equals("begin") && tok.isId("end")) ||
						tok.isId("end" + parent)) {
						do_next = false;
						break;
					} else if (parent.equals("fork") && 
							(tok.isId("join") || tok.isId("join_any") || tok.isId("join_none"))) {
						do_next = false;
						break;
					}
				}
				if (tok.isOp("(")) {
					start_of_scope(tok);
				} else if (tok.isOp(")")) {
					leave_scope();
				}
				tok = next_s();
			}
			if (do_next) {
				tok = next_s();
			}
		}
		
		if (fDebugEn) {
			debug("<-- indent_stmt parent=" + parent + " tok=" + tok.getImage());
		}
		
		return tok;
	}
	
	private SVIndentToken indent_constraint_block_or_stmt() {
		SVIndentToken tok = current_s();
		
		if (tok.isOp("{")) {
			start_of_scope(tok);
			tok = next_s();
			enter_scope(tok);
			
			while (!tok.isOp("}")) {
				tok = indent_constraint_block_or_stmt();
			}
			leave_scope(tok);
			
			tok = next_s();
		} else {
			tok = indent_constraint_stmt();
		}
		
		return tok;
	}

	private SVIndentToken indent_constraint_if_block_or_stmt() {
		SVIndentToken tok = current_s();
		
		if (tok.isOp("{")) {
			boolean begin_is_start_line = tok.isStartLine();
			
			if (begin_is_start_line) {
				enter_scope(tok);
			}
			tok = next_s();
			if (!begin_is_start_line) {
				enter_scope(tok);
			}
			
			while (!tok.isOp("}")) {
				tok = indent_constraint_block_or_stmt();
			}
			leave_scope(tok);
			
			tok = next_s();
		} else {
			enter_scope(tok);
			tok = indent_constraint_stmt();
			leave_scope(tok);
		}
		
		return tok;
	}

	private SVIndentToken indent_constraint_stmt() {
		SVIndentToken tok = current_s();
		
		if (tok.isId("if")) {
			tok = indent_constraint_if(false);
		} else if (tok.isOp("(")) {
			// very likely an implication statement
			tok = consume_expression();
			
			// (expr) -> [stmt | stmt_block]
			if (tok.isOp("->")) {
				tok = next_s();
				tok = indent_constraint_block_or_stmt();
			}
			// Otherwise, really don't know what's being specified
		} else {
			// Read a statement up to a semi-colon
			
			while (!tok.isOp(";")) {
				tok = next_s();
			}
			
			tok = next_s();
		}

		return tok;
	}
	
	private SVIndentToken indent_constraint_if(boolean is_else_if) {
		SVIndentToken tok = current();
		if (fDebugEn) {
			debug("--> indent_constraint_if() tok=" + tok.getImage());
		}
		
		start_of_scope(tok);
		
		tok = next_s();
		if (tok.isOp("(")) {
			tok = consume_expression();
		} else {
			// Doesn't seem right for an if
			return tok;
		}
		enter_scope(tok);
		
		tok = indent_constraint_if_block_or_stmt();
		
		if (tok.isId("else")) {
			tok = next_s();
			if (tok.isId("if")) {
				tok = indent_constraint_if(true);
			} else {
				tok = indent_constraint_block_or_stmt();
			}
		}
		
		if (fDebugEn) {
			debug("<-- indent_constraint_if() tok=" + 
				((tok != null)?tok.getImage():"null"));
		}
		
		return tok;
	}
	
	
	private SVIndentToken indent_case() {
		SVIndentToken tok = current();
		
		enter_scope(tok);
		
		tok = next_s(); // should be expression
		enter_scope(tok);
		
		tok = next_s();
		
		while (!tok.isId("endcase")) {
			while (!tok.isOp(":") && !tok.isId("endcase")) {
				tok = next_s();
			}
			
			if (tok.isOp(":")) {
				tok = next_s();
				tok = indent_block_or_statement("case", false);
			}
		}
		
		leave_scope();
		if (tok.isId("endcase")) {
			set_indent(tok, false);
		}
		
		tok = next_s();
		
		leave_scope();
		
		return tok;
	}

	/**
	 * start_of_scope()
	 * 
	 * Called before entry into a new scope. Increases the indent to apply
	 * to any comments between the current token and the first token in the
	 * new scope
	 * @param tok
	 */
	private void start_of_scope(SVIndentToken tok) {
		incr_indent(true);
		/*
		if (isAdaptiveTraining(tok)) {
		} else {
			push_indent_stack(peek_indent(), false);
		}
		 */

		// if (is_top_scope) {
		//	set_indent(tok, false);
		// }
		
		if (fDebugEn) {
			debug("start_of_scope() - indent=\"" + peek_indent() + "\"");
		}
	}

	private void end_of_scope() {
		end_of_scope(null);
	}
	
	private void end_of_scope(SVIndentToken tok) {
		// leave_scope(tok);
	}

	/**
	 * enter_scope()
	 * 
	 * Called with the first token of the new scope.
	 * In adaptive-indent mode, updates the  
	 * 
	 * @param tok
	 */
	private void enter_scope(SVIndentToken tok) {
		// boolean is_top_scope = (fIndentStack.size() == 1);
		// incr_indent(isAdaptiveTraining(tok));
		
		set_indent(tok, false);
		
		if (fDebugEn) {
			debug("enter_scope() - indent=\"" + peek_indent() + "\"");
		}
	}

	private void leave_scope() {
		leave_scope(null);
	}
	
	/**
	 * leave_scope()
	 * 
	 * @param tok
	 */
	private void leave_scope(SVIndentToken tok) {
		pop_indent(tok);
		if (fDebugEn) {
			debug("leave_scope() - indent=\"" + peek_indent() + "\"");
		}
	}
	
	private void push_indent_stack(String indent, boolean provisional) {
		if (fDebugEn) {
			debug("push_indent_stack: \"" + indent + "\" provisional=" + provisional);
		}
		fIndentStack.push(new Tuple<String, Boolean>(indent, provisional));
	}
	
	private String peek_indent() {
		return fIndentStack.peek().first();
	}
	
	private void incr_indent(boolean provisional) {
		push_indent_stack(fIndentStack.peek().first() + fIndentIncr, provisional);
		if (fDebugEn) {
			debug("incr_indent (provisional=" + provisional + ") - " +
					"indent=\"" + peek_indent() + "\"");
		}
	}

	private void pop_indent(SVIndentToken tok) {
		if (fIndentStack.size() > 1) {
			fIndentStack.pop();
		} else {
			if (fTestMode) {
				throw new RuntimeException("Indent stack out of sync");
			}
			
			if (fDebugEn) {
				debug("[ERROR] indent stack out of sync");
				ByteArrayOutputStream bos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(bos);

				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace(ps);
				}
				ps.flush();
				debug(bos.toString());
			}
		}
		
		if (tok != null) {
			set_indent(tok, false);
		}

		if (fDebugEn) {
			debug("pop_indent - indent=\"" + peek_indent() + "\"");
		}
	}
	
	private void set_indent(SVIndentToken tok, boolean implicit) {
		if (tok.isStartLine()) {
			if (isAdaptiveTraining(tok) && 
					fIndentStack.peek().second() &&
					!tok.isBlankLine()) {
				// If we are in the training period, the indent
				// level is provisional, and this is not a blank
				// line, then sample the indent
				if (fDebugEn) {
					debug("set_indent: convert implicit indent \"" + 
							fIndentStack.peek().first() + "\" to \"" +
							fCurrentIndent + "\"");
				}
				fIndentStack.peek().setFirst(fCurrentIndent);
			}
			debug("Set indent implicit=" + implicit + " \"" + tok.getImage() + "\" \"" + peek_indent() + "\"");
			tok.setLeadingWS(peek_indent());
		}
	}
	
	private void indent_multi_line_comment(SVIndentToken tok) {
		SVMultiLineIndentToken ml_comment = (SVMultiLineIndentToken)tok;
		
		if (tok.isStartLine()) {
			System.out.println("comment indent: \"" + peek_indent() + "\"");
			set_indent(tok, false);
			for (SVIndentToken line : ml_comment.getCommentLines()) {
				if (line.getImage().startsWith("*")) {
					line.setLeadingWS(peek_indent() + " ");
				}
			}
		} else {
			if (fDebugEn) {
				debug("Multi-line comment is not start-line");
			}
		}
	}
	
	private SVIndentToken consume_labeled_block(SVIndentToken tok) {
		if (tok.isOp(":")) {
			tok = next_s();
			tok = next_s();
		}
		return tok;
	}
	
	private SVIndentToken consume_expression() {
		SVIndentToken tok = current();
		int n_lbrace=0, n_rbrace=0;
		
		do {
			if (tok.isOp("(")) {
				n_lbrace++;
			} else if (tok.isOp(")")) {
				n_rbrace++;
			}
			tok = next_s();
		} while (n_lbrace != n_rbrace);
		
		return tok;
	}
	
	private boolean isAdaptiveTraining(SVIndentToken tok) {
		return (fAdaptiveIndentEnd != -1 && tok.getLineno() <= fAdaptiveIndentEnd);
	}
	
	private SVIndentToken next() {
		SVIndentToken tok = null;
		
		while ((tok = fScanner.next()) != null &&
				(tok.getType() == SVIndentTokenType.BlankLine ||
					tok.getType() == SVIndentTokenType.MultiLineComment ||
					tok.getType() == SVIndentTokenType.SingleLineComment ||
					(tok.isPreProc() && fPreProcDirectives.contains(tok.getImage())))) {
			if (tok.getType() == SVIndentTokenType.SingleLineComment) {
				set_indent(tok, true);
				fTokenList.add(tok);
			} else if (tok.getType() == SVIndentTokenType.MultiLineComment) {
				indent_multi_line_comment(tok);
				fTokenList.add(tok);
			} else if (tok.isPreProc()) {
				// If this is a built-in directive, then place at the
				// beginning of the line
				Stack<Tuple<String, Boolean>> stack = fIndentStack;
				fIndentStack = new Stack<Tuple<String,Boolean>>();
				push_indent_stack("", false);
				set_indent(tok, true);
				while (tok != null && !tok.isEndLine()) {
					//fTokenList.add(tok);
					fTokenList.add(tok);
					tok = fScanner.next();
					if (fDebugEn) {
						debug("pre-proc line: " + ((tok != null)?tok.getImage():"null"));
					}
				}
				
				if (tok != null) {
					fTokenList.add(tok);
				}
				fIndentStack = stack;
			} else {
				fTokenList.add(tok);
			}
		}
		
		if (tok != null) {
			if (tok.isOp("(")) {
				if (fNLeftParen == fNRightParen) {
// TODO:					enter_scope(tok);
				}
				fNLeftParen++;
			} else if (tok.isOp(")")) {
				fNRightParen++;
				if (fNLeftParen == fNRightParen) {
// TODO:					leave_scope(tok);
					fNLeftParen = fNRightParen = 0;
				}
			}
			if (tok.isStartLine()) {
				fCurrentIndent = tok.getLeadingWS();
				set_indent(tok, true);
			}
			fTokenList.add(tok);
		}
		
		fCurrent = tok;

		return tok;
	}
	
	private SVIndentToken current() {
		return fCurrent;
	}
	
	private SVIndentToken current_s() {
		if (current() == null) {
			throw new RuntimeException();
		}
		
		return current();
	}
	
	private SVIndentToken next_s() {
		SVIndentToken ret = next();
		
		if (fDebugEn) {
			if (ret != null) {
				debug("next_s: " + ret.getImage());
			} else {
				debug("next_s: null");
			}
		}
		
		if (ret == null) {
			throw new IndentEOFException();
		}
		// Return the last
		return ret;
	}

	private static String get_end_kw(String kw) {
		if (kw.equals("covergroup")) {
			return "endgroup";
		} else {
			return "end" + kw;
		}
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
			System.out.println("[INDENT] " + msg);
		}
	}
}

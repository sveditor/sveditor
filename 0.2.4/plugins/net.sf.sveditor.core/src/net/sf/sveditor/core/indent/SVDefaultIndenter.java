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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDefaultIndenter {
	private ISVIndentScanner				fScanner;
	private Stack<String>					fIndentStack;
	private List<SVIndentToken>				fTokenList;
	private SVIndentToken					fCurrent;
	private String							fCurrentIndent;
	private LogHandle						fLog;
	private int								fQualifiers;
	private static final boolean			fDebugEn = false;
	private int								fNLeftParen, fNRightParen;
	
	private boolean							fAdaptiveIndent = false;
	private int								fAdaptiveIndentEnd;

	
	static private Map<String, Integer>		fQualifierMap;
	static private Set<String>				fPreProcDirectives;

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
	
	public SVDefaultIndenter() {
		fIndentStack = new Stack<String>();
		fTokenList = new ArrayList<SVIndentToken>();
		fLog = LogFactory.getLogHandle("SVDefaultIndenter");
	}
	
	public void setAdaptiveIndent(boolean adaptive) {
		fAdaptiveIndent = adaptive;
	}
	
	public void setAdaptiveIndentEnd(int lineno) {
		fAdaptiveIndentEnd = lineno;
	}
	
	public void init(ISVIndentScanner scanner) {
		fScanner = scanner;
		fIndentStack.push("");
	}
	
	public String indent() {
		return indent(-1, -1);
	}
	
	public boolean isQualifierSet(String key) {
		return ((fQualifierMap.get(key) & fQualifiers) != 0);
	}

	public String indent(int start_line, int end_line) {
		StringBuilder sb = new StringBuilder();
		SVIndentToken 	tok;
		
		fNLeftParen = fNRightParen = 1;
		
		while ((tok = next_i()) != null) {
			
			// Scan forward until the end of the token list or until we find
			// a keyword
			try {
				do {
					if (tok.getType() == SVIndentTokenType.Identifier &&
							fQualifierMap.containsKey(tok.getImage())) {
						fQualifiers |= fQualifierMap.get(tok.getImage());
						tok = next_i();
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
						tok = next_i();
					} else {
						tok = next_i();
					} 
				} while ((tok = current()) != null);
			} catch (RuntimeException e) {
				// e.printStackTrace();
				break;
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
	
	public String getLine(int lineno) {
		StringBuilder sb = new StringBuilder();
		
		for (int i=0; i<fTokenList.size(); i++) {
			SVIndentToken t = fTokenList.get(i);
			
			if (t.getLineno() == lineno) {
				for (int j=i; j<fTokenList.size(); j++) {
					t = fTokenList.get(j);
					if (t.getLineno() == lineno) {
						sb.append(t.getLeadingWS() + 
								t.getImage() +
								t.getTrailingWS() +
								((t.isEndLine())?"\n":""));
					} else {
						break;
					}
				}
				break;
			}
		}
		
		return sb.toString();
	}
	
	private SVIndentToken indent_if(boolean is_else_if) {
		boolean non_block_stmt = false;
		SVIndentToken tok = current();

		if (!is_else_if) {
			enter_scope(tok);
		}
		
		if (fDebugEn) {
			debug("--> indent_if() tok=" + tok.getImage());
		}
		
		tok = next_s();
		
		if (tok.isOp("(")) {
			tok = consume_expression();
		} else {
			//System.out.println("[ERROR] unsure what happened - tok=" + 
		    // tok.getImage());
			// bail out -- not sure what happened...
			return tok;
		}
		
		if (!tok.isId("begin")) {
			push_indent(tok);
			non_block_stmt = true;
		}
		
		tok = indent_block_or_statement(null);
		
		if (non_block_stmt) {
			pop_indent(tok);
		}
		
		if (tok.isId("else")) {
			tok = next_s();
			if (tok.isId("if")) {
				tok = indent_if(true);
			} else {
				non_block_stmt = false;
				if (!tok.isId("begin")) {
					push_indent(tok);
					non_block_stmt = true;
				}
				
				tok = indent_block_or_statement(null);
				
				if (non_block_stmt) {
					pop_indent(tok);
				}
			}
		}
		
		if (fDebugEn) {
			debug("<-- indent_if() tok=" + 
				((tok != null)?tok.getImage():"null"));
		}
		
		if (!is_else_if) {
			leave_scope(); // get rid of scope indent
		}
		
		return tok;
	}
	
	private SVIndentToken indent_fork() {
		SVIndentToken tok = current();
		
		enter_scope(tok);

		tok = next_s();
		push_indent(tok);

		while (!tok.isId("join") && 
				!tok.isId("join_none") && 
				!tok.isId("join_any")) {
			
			tok = indent_stmt("fork");
		}
		pop_indent(tok);
		
		tok = next_s();
		
		leave_scope();
		
		return tok;
	}
	
	private SVIndentToken indent_loop_stmt() {
		boolean non_block_stmt = false;
		SVIndentToken tok, first;
		
		tok = first = current();
		
		enter_scope(tok);
		
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
		
		if (!tok.isId("begin")) {
			push_indent(tok);
			non_block_stmt = true;
		}
		
		tok = indent_block_or_statement(null);
		
		if (non_block_stmt) {
			pop_indent(tok);
		}

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
		
		leave_scope();
		
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

			push_indent(tok);
			
			while (!tok.isOp("}")) {
				tok = next_s();
			}
			pop_indent(tok);
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
		
		enter_scope(tok); 	// establish the indent of this scope
		                    // for adaptive-indent purposes
		
		String end = get_end_kw(item);
		if (fDebugEn) {
			debug("--> indent_ifc_module_class(" + item + ")");
		}

		tok = next_s();
		// push indent for the port list
		push_indent(tok);
		
		// Reach the end of the declaration
		while (!tok.isOp(";")) {
			tok = next_s();
		}
		pop_indent(null); // pop indent for the declaration

		// Logic hole: Any comments scanned by next_s() will
		// be indented at the pre-set indent level. This indent
		// level is not what we desire
		
		List<SVIndentToken> tok_l = next_l();
		push_indent(tok_l);
		tok = tok_l.get(tok_l.size()-1);
		
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
				boolean not_block = false;
				enter_scope(tok);
				
				tok = next_s();
				
				if (tok.isOp("@")) {
					tok = next_s(); // paren
					tok = consume_expression();
				}
				
				if (!tok.isId("begin")) {
					not_block = true;
					push_indent(tok);
				}
				
				tok = indent_block_or_statement(null);
				
				if (not_block) {
					pop_indent(tok);
				}
				leave_scope();
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
				tok = indent_block_or_statement(item);
			}
		}
		
		pop_indent(tok);
		
		tok = consume_labeled_block(next_s());
		
		if (fDebugEn) {
			debug("--> indent_ifc_module_class(" + item + ") next=" + 
				((tok != null)?tok.getImage():"null"));
		}
		
		leave_scope(); // restore scope previously set
		return tok;
	}

	private SVIndentToken indent_covergroup() {
		SVIndentToken tok = current_s();
		
		enter_scope(tok);
		
		if (fDebugEn) {
			debug("--> indent_covergroup()");
		}
		
		// Reach the end of the declaration
		while (tok != null && !tok.isOp(";")) {
			tok = next_s();
		}
		
		tok = next_s();
		push_indent(tok);
		
		// Now, read body items
		while (tok != null) {
		
			if (tok.isId("endgroup")) {
				break;
			} else {
				tok = indent_covergroup_item();
			}
		}
		
		pop_indent(tok);
		
		tok = next_s();
		
		if (fDebugEn) {
			debug("--> indent_covergroup() next=" +
				((tok != null)?tok.getImage():"null"));
		}
		
		leave_scope();
		
		return tok;
	}
	
	private SVIndentToken indent_constraint() {
		SVIndentToken tok = current_s();
		
		enter_scope(tok);
		
		tok = next_s(); // name of constraint
		
		tok = next_s(); // Should be '{'
		
		if (!tok.isOp("{")) {
			// Not sure what happened...
			return tok;
		}
		
		tok = next_s();
		push_indent(tok);
		
		while (!tok.isOp("}")) {
			tok = indent_constraint_stmt();
		}
		
		pop_indent(tok);
		
		tok = next_s();
		
		leave_scope();
		
		return tok;
	}
	
	private SVIndentToken indent_covergroup_item() {
		SVIndentToken tok = current();
		
		enter_scope(tok);
		
		// Scan to the end of the statement / beginning of the block
		tok = next_s();
		push_indent(tok);
		while (!tok.isOp(";") && !tok.isOp("{")) {
			tok = next_s();
		}
		pop_indent(null);
		
		if (tok.isOp("{")) {
			boolean do_indent = true;
			int lb_count = 1, rb_count = 0;
			
			do {
				tok = next_s();
				if (do_indent) {
					push_indent(tok);
					do_indent = false;
				}
				if (tok.isOp("{")) {
					lb_count++;
					do_indent = true;
				} else if (tok.isOp("}")) {
					rb_count++;
					pop_indent(tok);
				}
			} while (lb_count != rb_count);
			
			/*
			pop_indent();
			set_indent(tok);
			 */
		}
		
		tok = next_s();
		
		leave_scope();
		
		return tok;
	}

	private SVIndentToken indent_task_function(String item) {
		SVIndentToken tok = current_s();
		
		enter_scope(tok);
		
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
			List<SVIndentToken> tok_l = next_l();
			push_indent(tok_l);
			tok = tok_l.get(tok_l.size()-1);
			
			while (tok != null) {
				if (tok.isId(end)) {
					break;
				} else {
					tok = indent_block_or_statement(item);
				}
			}
			pop_indent(tok);
			
			tok = consume_labeled_block(next_s());
		} else {
			tok = next_s();
		}

		
		if (fDebugEn) {
			debug("--> indent_task_function(" + item + ") " +
				((tok != null)?tok.getImage():"null"));
		}
		
		leave_scope();
		
		return tok;
	}
	
	private SVIndentToken indent_block_or_statement(String parent) {
		SVIndentToken tok = current();
		if (fDebugEn) {
			debug("--> indent_block_or_statement() tok=" + tok.getImage());
		}
		
		if (tok.isId("begin")) {
			parent = "begin";
			
			// Ensure that any comments at the beginning of the
			// block are indented correctly
			List<SVIndentToken> tok_l = next_l();
			push_indent(tok_l);
			tok = tok_l.get(tok_l.size()-1);
			
			while (tok != null) {
				if (fDebugEn) {
					debug("top of begin/end loop: " + tok.getType() + " " + tok.getImage());
				}
				if (tok.isId("end")) {
					pop_indent(tok);
					if (fDebugEn) {
						debug("Setting indent \"" + get_indent() + "\"");
					}
					tok = next_s();
					
					tok = consume_labeled_block(tok);
					break;
				} else {
					tok = indent_block_or_statement(parent);
				}
			}
		} else {
			tok = indent_stmt(parent);
		}

		if (fDebugEn) {
			debug("<-- indent_block_or_statement() tok=" + 
				((tok != null)?tok.getImage():"null") + " parent=" + parent);
		}
		
		return tok;
	}
	
	private SVIndentToken indent_stmt(String parent) {
		SVIndentToken tok = current_s();
		
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
				indent_block_or_statement(null);
			}
			leave_scope();
		} else if (tok.isId("typedef")) {
			tok = indent_typedef();
		} else if (tok.isId("while") || tok.isId("do") ||
				tok.isId("repeat") || tok.isId("forever") ||
				tok.isId("for") || tok.isId("foreach")) {
			tok = indent_loop_stmt();
		} else if (tok.isPreProc()) {
			boolean do_indent = true;
			// For now, just read the line. This could be a problem in some cases
			while (!tok.isOp(";") && !tok.isEndLine()) {
				tok = next_s();
				if (do_indent) {
					push_indent(tok);
					do_indent = false;
				}
			}
			pop_indent(null);
			tok = next_s();
		} else {
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
				tok = next_s();
			}
			if (do_next) {
				tok = next_s();
			}
		}
		
		return tok;
	}
	
	private SVIndentToken indent_constraint_block_or_stmt() {
		SVIndentToken tok = current_s();
		
		if (tok.isOp("{")) {
			tok = next_s();
			push_indent(tok);
			
			while (!tok.isOp("}")) {
				tok = indent_constraint_block_or_stmt();
			}
			pop_indent(tok);
			
			tok = next_s();
		} else {
			tok = indent_constraint_stmt();
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
		boolean non_block_stmt = false;
		SVIndentToken tok = current();
		if (fDebugEn) {
			debug("--> indent_constraint_if() tok=" + tok.getImage());
		}
		
		if (!is_else_if) {
			enter_scope(tok);
		}
		
		tok = next_s();
		if (tok.isOp("(")) {
			tok = consume_expression();
		} else {
			// Doesn't seem right for an if
			return tok;
		}
		
		if (!tok.isOp("{")) {
			push_indent(tok);
			non_block_stmt = true;
		}
		
		tok = indent_constraint_block_or_stmt();
		
		if (non_block_stmt) {
			pop_indent(tok);
		}
		
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
		
		if (!is_else_if) {
			leave_scope();
		}
		
		return tok;
	}
	
	
	private SVIndentToken indent_case() {
		SVIndentToken tok = current();
		
		enter_scope(tok);
		
		tok = next_s(); // should be expression
		push_indent(tok);
		
		tok = next_s();
		
		while (!tok.isId("endcase")) {
			while (!tok.isOp(":") && !tok.isId("endcase")) {
				tok = next_s();
			}
			
			if (tok.isOp(":")) {
				tok = next_s();
				tok = indent_block_or_statement("case");
			}
		}
		
		pop_indent(null);
		if (tok.isId("endcase")) {
			set_indent(tok);
		}
		
		tok = next_s();
		
		leave_scope();
		
		return tok;
	}
	
	private void enter_scope(SVIndentToken tok) {
		push_indent(tok, true);
	}
	
	private void leave_scope() {
		pop_indent(null);
	}
	
	private void push_indent(SVIndentToken tok) {
		push_indent(tok, false);
	}

	private void push_indent(List<SVIndentToken> tok_l) {
		if (fAdaptiveIndent && fAdaptiveIndentEnd >= 0 && tok_l.get(0).getLineno() <= fAdaptiveIndentEnd) {
			// Still in the training period. We don't want to take any 
			// indent hints from white-space only lines. So, we just set existing
			// indent for these lines. Then, take our indent hints from the first non-WS line
			int idx = 0;
			while (idx < tok_l.size() && tok_l.get(idx).isBlankLine()) {
				set_indent(tok_l.get(idx));
				idx++;
			}
			if (idx < tok_l.size()) {
				push_indent(tok_l.get(idx), false);
				idx++;
			}
			while (idx < tok_l.size()) {
				set_indent(tok_l.get(idx));
				idx++;
			}
		} else {
			// If not in adaptive training mode, we set the indent of the first
			// line, then have subsequent lines follow that indent
			push_indent(tok_l.get(0), false);
			for (int i=1; i<tok_l.size(); i++) {
				set_indent(tok_l.get(i));
			}
		}
	}

	private void push_indent(SVIndentToken tok, boolean just_sample) {
		if (fAdaptiveIndent) {
			if (fAdaptiveIndentEnd == -1 || tok.getLineno() > fAdaptiveIndentEnd) {
				if (fDebugEn) {
					fLog.debug("push_indent: past training period (" + tok.getImage() + ")");
				}
				// Indent based on the previous
				if (just_sample) {
					if (fDebugEn) {
						debug("push_indent: just_sample");
					}
					fIndentStack.push(fIndentStack.peek());
				} else {
					if (fDebugEn) {
						debug("push_indent: indent");
					}
					fIndentStack.push(fIndentStack.peek() + "\t");
				}
				set_indent(tok);

				/*
				if (!just_sample) {
					fIndentStack.push(fIndentStack.peek() + "\t");
				}
				 */
			} else {
				if (fDebugEn) {
					fLog.debug("push_indent: training period isStart=" + tok.isStartLine() + " tok=" + tok.getImage());
				}
				// Save the current indent
				if (tok.isStartLine()) {
					if (fDebugEn) {
						fLog.debug(tok.getLineno() + ": push existing indent: \"" + fCurrentIndent + "\"");
					}
					fIndentStack.push(fCurrentIndent);
				} else {
					if (fDebugEn) {
						fLog.debug(tok.getLineno() + ": push last line-start indent: \"" + fCurrentIndent + "\"");
					}
					fIndentStack.push(fCurrentIndent);
				}
			}
			set_indent(tok);
		} else {
			// If we're just sampling in non-adaptive mode, then just
			// copy the previous level's indent
			if (just_sample) {
				if (fDebugEn) {
					debug("push_indent: just_sample");
				}
				fIndentStack.push(fIndentStack.peek());
			} else {
				if (fDebugEn) {
					debug("push_indent: indent");
				}
				fIndentStack.push(fIndentStack.peek() + "\t");
			}
			set_indent(tok);
		}
	}
	
	private void pop_indent(SVIndentToken tok) {
		if (fDebugEn) {
			debug("pop_indent");
		}
		if (fIndentStack.size() > 1) {
			fIndentStack.pop();
		}
		
		if (tok != null) {
			set_indent(tok);
		}
	}
	
	private String get_indent() {
		return fIndentStack.peek();
	}
	
	private void set_indent(SVIndentToken tok) {
		if (tok.isStartLine()) {
			tok.setLeadingWS(get_indent());
		}
	}
	
	private void indent_multi_line_comment(SVIndentToken tok) {
		SVMultiLineIndentToken ml_comment = (SVMultiLineIndentToken)tok;
		
		if (tok.isStartLine()) {
			set_indent(tok);
			for (SVIndentToken line : ml_comment.getCommentLines()) {
				if (line.getImage().startsWith("*")) {
					line.setLeadingWS(get_indent() + " ");
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
	
	private List<SVIndentToken> next() {
		List<SVIndentToken> ret = new ArrayList<SVIndentToken>();
		SVIndentToken tok = null;
		
		while ((tok = fScanner.next()) != null &&
				(tok.getType() == SVIndentTokenType.BlankLine ||
					tok.getType() == SVIndentTokenType.MultiLineComment ||
					tok.getType() == SVIndentTokenType.SingleLineComment ||
					(tok.isPreProc() && fPreProcDirectives.contains(tok.getImage())))) {
			if (tok.getType() == SVIndentTokenType.SingleLineComment) {
				set_indent(tok);
				ret.add(tok);
				// fTokenList.add(tok);
			} else if (tok.getType() == SVIndentTokenType.MultiLineComment) {
				indent_multi_line_comment(tok);
				// fTokenList.add(tok);
				ret.add(tok);
			} else if (tok.isPreProc()) {
				// If this is a built-in directive, then place at the
				// beginning of the line
				Stack<String> stack = fIndentStack;
				fIndentStack = new Stack<String>();
				fIndentStack.push("");
				set_indent(tok);
				while (tok != null && !tok.isEndLine()) {
					//fTokenList.add(tok);
					ret.add(tok);
					tok = fScanner.next();
					if (fDebugEn) {
						debug("pre-proc line: " + ((tok != null)?tok.getImage():"null"));
					}
				}
				
				if (tok != null) {
					//fTokenList.add(tok);
					ret.add(tok);
				}
				fIndentStack = stack;
			} else {
				//fTokenList.add(tok);
				ret.add(tok);
			}
		}
		
		if (tok != null) {
			if (tok.isOp("(")) {
				if (fNLeftParen == fNRightParen) {
// TODO:					push_indent();
					fIndentStack.push(fIndentStack.peek() + "\t");
				}
				fNLeftParen++;
			} else if (tok.isOp(")")) {
				fNRightParen++;
				if (fNLeftParen == fNRightParen) {
					pop_indent(null);
					fNLeftParen = fNRightParen = 0;
				}
			}
			if (tok.isStartLine()) {
				fCurrentIndent = tok.getLeadingWS();
				set_indent(tok);
			}
			// fTokenList.add(tok);
			ret.add(tok);
		}
		
		fCurrent = tok;
		fTokenList.addAll(ret);
		
		return (tok != null)?ret:null;
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
		List<SVIndentToken> ret = next();
		
		if (fDebugEn) {
			if (ret != null) {
				for (SVIndentToken t : ret) {
					debug("next_s: " + t.getImage());
				}
			} else {
				debug("next_s: null");
			}
		}
		
		if (ret == null) {
			throw new RuntimeException();
		}
		// Return the last
		return ret.get(ret.size()-1);
	}

	private List<SVIndentToken> next_l() {
		List<SVIndentToken> ret = next();
		
		if (fDebugEn) {
			if (ret != null) {
				for (SVIndentToken t : ret) {
					debug("next_l: " + t.getImage());
				}
			} else {
				debug("next_l: null");
			}
		}
		
		if (ret == null) {
			throw new RuntimeException();
		}
		
		// Return the last
		return ret;
	}

	private SVIndentToken next_i() {
		List<SVIndentToken> ret = next();
		
		if (fDebugEn) {
			if (ret != null) {
				for (SVIndentToken t : ret) {
					debug("next_l: " + t.getImage());
				}
			} else {
				debug("next_l: null");
			}
		}
		
		if (ret == null) {
			return null;
		} else {
			return ret.get(ret.size()-1);
		}
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
		}
	}
}

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
import java.util.regex.Pattern;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

/**
 * 
 * @author ballance
 *
 * Implementation pattern:
 * - <start_of_scope> should be called before the first token of a new scope
 *   - provisionally sets the new indent level
 *   - Any comments will use this indent level prior to the first real token
 *     in the scope
 * - <enter_scope> should be called on the first token of the new scope.
 *   - In adaptive indent mode, synchronizes the provisional indent level
 *     with the actual indent level
 * - <leave_scope> should be called to exit a scope. It typically should
 *     be called with the last token of the scope, provided that can be determined
 */
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
	private Pattern							fTabReplacePattern;
	
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
	
	public void setIndentIncr(String incr) {
		fIndentIncr = incr;
		if (fIndentIncr.charAt(0) != '\t') {
			// Want to replace any existing tabs with
			// the indent increment
			fTabReplacePattern = Pattern.compile("\t");
		} else {
			fTabReplacePattern = null;
		}
	}
	
	public void setAdaptiveIndentEnd(int lineno) {
		fAdaptiveIndentEnd = lineno;
	}
	
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
							tok.isId("package") || tok.isId("sequence") ||
							tok.isId("property")) {
						tok = indent_ifc_module_class(tok.getImage());
						fQualifiers = 0;
					} else if (tok.isId("config")) {
						tok = indent_config(tok.getImage());
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
//				String leading_ws = t.getLeadingWS();
				String leading_ws = t.getLeadingNonNewLineWS();
				// Replace any tabs in the leading whitespace
				// if we're inserting spaces instead of tabs
				if (t.isStartLine() && fTabReplacePattern != null) {
					leading_ws = fTabReplacePattern.matcher(leading_ws).replaceAll(fIndentIncr);
				}
				sb.append(leading_ws + 
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
				ret = t.getLeadingNonNewLineWS();
				
				// Replace any tabs in the leading whitespace
				// if we're inserting spaces instead of tabs
				if (t.isStartLine() && fTabReplacePattern != null) {
					ret = fTabReplacePattern.matcher(ret).replaceAll(fIndentIncr);
				}
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
			// Insert a dummy scope to prevent the token following the 'else'
			// from re-setting the adaptive indent
			start_of_scope(tok, false);
			if (fDebugEn) {
				debug("--> else next_s");
			}
			tok = next_s();
			if (fDebugEn) {
				debug("<-- else next_s");
			}
			leave_scope();
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
	
	private SVIndentToken indent_assert (boolean is_else_if) {
		SVIndentToken tok = current();
		
		if (fDebugEn) {
			debug("--> indent_if() tok=" + tok.getImage());
		}
		start_of_scope(tok);

		tok = next_s();

		if (tok.isOp("(")) {
			tok = consume_expression();
			if (tok.isOp(";"))  {
				tok = next_s();
				leave_scope (tok);
				return tok;
			}
		} else {
			//System.out.println("[ERROR] unsure what happened - tok=" + 
			// tok.getImage());
			// bail out -- not sure what happened...
			return tok;
		}

		if (tok.isId("else")) {
			leave_scope(tok);		// un-indent, we already indented before we came here, assuming it was a single-line bit of code
//			start_of_scope(tok);
		}
		else  {
			tok = indent_if_stmts(null);
		}
		if (tok.isId("else")) {
			// Insert a dummy scope to prevent the token following the 'else'
			// from re-setting the adaptive indent
			start_of_scope(tok, false);
			if (fDebugEn) {
				debug("--> else next_s");
			}
			tok = next_s();
			if (fDebugEn) {
				debug("<-- else next_s");
			}
			leave_scope();
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
				leave_scope(tok);		// un-indent, we already indented before we came here, assuming it was a single-line bit of code
				start_of_scope(tok);
			}
			// begin often has : <label>  consume this if it is there
			tok = consume_labeled_block(next_s());
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
					tok = consume_labeled_block(next_s());
					break;
				} else {
					// Indent statement. Note that we're already in the
					// scope that the statement should be in
					tok = indent_block_or_statement(parent, true);
				}
			}
		} else {
			// No begin
			enter_scope(tok);
//			tok = indent_stmt(parent, true);
			tok = indent_stmt(parent, false);
			leave_scope(tok);
		}
		
		return tok;
	}
	
	private SVIndentToken indent_fork() {
		SVIndentToken tok = current();
		
		start_of_scope(tok);
		tok = next_s();
		enter_scope(tok);

		while (tok != null && 
				!tok.isId("join") && 
				!tok.isId("join_none") && 
				!tok.isId("join_any")) {
			
			tok = indent_block_or_statement("fork", true);
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
		boolean enum_struct = false;
		
		start_of_scope(tok);
		
		if (fDebugEn) {
			debug("--> indent_typedef()");
		}
		
		tok = next_s();
		
		if (tok.isId("enum") || tok.isId("struct") || tok.isId("union")) {
			tok = indent_struct_union_enum("typedef");
			enum_struct = true;
		}

		// read to the end of the statement
		while (!tok.isOp(";")) {
			tok = next_s();
		}
		tok = next_s();
		
		if (fDebugEn) {
			debug("<-- indent_typedef()");
		}

		if (!enum_struct) {
			// We've already left the scope (adjusting the closing brace) 
			// in the case of an enum or struct
			leave_scope(tok);
		}
		return tok;
	}

	private SVIndentToken indent_struct_union_enum(String parent) {
		SVIndentToken tok = next_s(); // advance beyond struct/union
		
		if (!parent.equals("typedef")) {
			start_of_scope(tok);
		}
		
		while (!tok.isOp("{", ";")) {
			tok = next_s();
		}
		
		if (tok.isOp("{")) {
			// Not a forward declaration
			tok = next_s();
			if (!tok.isOp("}")) {
				enter_scope(tok);
			}

			while (!tok.isOp("}")) {
				tok = next_s();
			}
		}
		// Leave on the closing brace
//		if (!parent.equals("typedef")) {
			leave_scope(tok);
//		}
		
//		tok = next_s();
		
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
			} else if (tok.isId("class") || tok.isId("module") || tok.isId("interface") ||
					tok.isId("property") || tok.isId("sequence")) {
				tok = indent_ifc_module_class(tok.getImage());
				fQualifiers = 0;
			} else if (tok.isId("struct") || tok.isId("union") || tok.isId("enum")) {
				tok = indent_struct_union_enum("");
				fQualifiers = 0;
			} else if (is_always(tok))  {
				tok = indent_always();
			} else if (tok.isId("initial") || tok.isId("final")) {
				tok = next_s();
				tok = indent_block_or_statement(null, false);
				fQualifiers = 0;
			} else if (tok.isId("generate")) {
				tok = next_s();
				tok = indent_generate();
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
	/**
	 * indent_ifc_module_class()
	 * 
	 * Indents a class, module or interface and the items
	 * within the body
	 * 
	 * @param item
	 * @return
	 */
	private SVIndentToken indent_config(String item) {
		SVIndentToken tok = current_s();
		
		String end = "endconfig";
		if (fDebugEn) {
			debug("--> indent_config(" + item + ")");
		}

		start_of_scope(tok); 	// establish the indent of this scope
        // for adaptive-indent purposes

		tok = next_s();
		
		// Reach the end of the declaration
		while (!tok.isOp(";")) {
			tok = next_s();
		}
		
		tok = next_s();
		enter_scope(tok); // enter the body of the module
		
		fQualifiers = 0;
		
		// Now, read body items
		while (tok != null) {
			
			if (tok.isId(end)) {
				break;
			} else {
				tok = indent_block_or_statement(item, true);
			}
		}
		
		leave_scope(tok);
		end_of_scope(tok); // restore scope previously set
		
		tok = consume_labeled_block(next_s());
		
		if (fDebugEn) {
			debug("--> indent_config (" + item + ") next=" + 
				((tok != null)?tok.getImage():"null"));
		}
		
		return tok;
	}

	private static boolean is_always(SVIndentToken tok) {
		return (tok.isId("always") || tok.isId("always_comb") ||
				tok.isId("always_latch") || tok.isId("always_ff") ||
				tok.isOp("@"));
	}

	/**
	 * This function will check to see if the given token is an open brace
	 * Currently checks for ({[
	 * 
	 * @param tok - token to be evaluated
	 * @return
	 */
	private static boolean is_open_brace (SVIndentToken tok) {
		return (tok.isOp("(") || tok.isOp("{") ||
				tok.isOp("["));
	}
	
	/**
	 * This function will check to see if the given token is an open brace
	 * Currently checks for ({[
	 * 
	 * @param tok - token to be evaluated
	 * @return
	 */
	private static boolean is_close_brace (SVIndentToken tok) {
		return (tok.isOp(")") || tok.isOp("}") ||
				tok.isOp("]"));
	}
	
	/**
	 * Checks to see if id is one of the "normal" case statements:
	 *  - case
	 *  - casez
	 *  - casex
	 * @param tok
	 * @return boolean, true if is a match
	 */
	private static boolean is_case(SVIndentToken tok) {
//		return (tok.isId("case"));
		return (tok.isId("case") || tok.isId("casez") ||
				tok.isId("casex"));
	}
	
	private SVIndentToken indent_covergroup() {
		int level = fIndentStack.size();
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
		
		if (fTestMode) {
			if (level != fIndentStack.size()) {
				throw new RuntimeException("Indent stack out-of-sync: " + 
						"entry=" + level + " exit=" + fIndentStack.size());
			}
		}
		
		return tok;
	}
	
	private SVIndentToken indent_generate() {
		int level = fIndentStack.size();
		SVIndentToken tok = current_s();
		
		if (fDebugEn) {
			debug("--> indent_generate()");
		}
		
		while (tok != null) {
			
			if (tok.isId("endgenerate")) {
				break;
			} else {
				tok = indent_block_or_statement(null, false);
			}
		}
		
		tok = next_s();
		
		if (fDebugEn) {
			debug("--> indent_generate() next=" +
					((tok != null)?tok.getImage():"null"));
		}
		
		if (fTestMode) {
			if (level != fIndentStack.size()) {
				throw new RuntimeException("Indent stack out-of-sync: " + 
						"entry=" + level + " exit=" + fIndentStack.size());
			}
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
		int level = fIndentStack.size();
		SVIndentToken tok = current();
		int lb_count = 0, rb_count = 0;
		
		if (fDebugEn) {
			debug("--> indent_covergroup_item: " + tok.getImage());
		}
		
		// Scan to the end of the statement / beginning of the block
		start_of_scope(tok);
		tok = next_s();
//MSB:		enter_scope(tok);
		boolean keep_going = true;
		boolean block_leave_scope = false;
		while (keep_going)  {
			
			if (tok.isOp(";") && (lb_count == rb_count)) {
				keep_going = false;
				leave_scope(); // leave coverpoint-declaration indent scope
				tok = next_s();
			} else if (tok.isOp("{")) {
				// This is the opening brace for the coverpoint. We need to
				// leave the scope for the second-line indent of the coverpoint
				if (lb_count == 0 && !block_leave_scope) {
					leave_scope(); // leave coverpoint-declaration indent scope
					block_leave_scope = true;
				}
				lb_count ++;
				start_of_scope(tok);
				tok = next_s();
				enter_scope(tok);
			} else if (tok.isOp("}")) {
				rb_count++;
				leave_scope(tok);
				tok = next_s();
				// Check to see if we have a case where we have an } {
				if (tok.isOp("{"))  {
					lb_count ++;
					start_of_scope(tok);
					tok = next_s();
				}
				if (lb_count == rb_count)  {
					keep_going = false;
//					leave_scope(tok);
				}
			}
			else  {
				tok = next_s();
			}
		}
//MSB:		leave_scope(tok);
		
		if (fDebugEn) {
			debug("<-- indent_covergroup_item: " + tok.getImage());
		}
		
		if (fTestMode) {
			if (level != fIndentStack.size()) {
				throw new RuntimeException("Indent stack out-of-sync: " + 
						"entry=" + level + " exit=" + fIndentStack.size());
			}
		}
		
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
	
	/**
	 * 
	 * @param parent - if parent is begin, will do appropriate things with begin statement
	 * @param parent_is_block - If this is false, the statements will be indented, else treated as previously indented
	 * @return
	 */
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
			// begin often has : <label>  consume this if it is there
			tok = consume_labeled_block(next_s());

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
					tok = consume_labeled_block(next_s());
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
			tok = indent_stmt(parent, !parent_is_block);
			
			if (!parent_is_block) {
				leave_scope(tok);
			}
		}

		if (fDebugEn) {
			debug("<-- indent_block_or_statement() tok=" + 
				((tok != null)?tok.getImage():"null") + " parent=" + parent);
		}
		
		return tok;
	}
	
	/**
	 * This thing figures out what kind of statment we have to deal with, and calls
	 * the appropriate indenter (if/for/case etc)
	 * @param parent
	 * @return
	 */
	private SVIndentToken indent_stmt(String parent, boolean parent_is_block) {
		SVIndentToken tok = current_s();
		
		if (fDebugEn) {
			debug("--> indent_stmt parent=" + parent + " tok=" + tok.getImage() + " parent_is_block=" + parent_is_block);
		}
		
		// Just indent the statement
		if (tok.isId("if")) {
			tok = indent_if(false);
		} else if (tok.isId("assert")) {
			tok = indent_assert(false);
		} else if (tok.isId("fork")) {
			tok = indent_fork();
		} else if (is_case(tok) || tok.isId("randcase")) {
			tok = indent_case();
		} else if (is_always(tok))  {
			tok = indent_always();
		} else if (tok.isId("initial") || tok.isId("final")) {
			// enter_scope(tok);
			tok = next_s();
			tok = indent_block_or_statement(null, false);
		} else if (tok.isId("assign")) {
			tok = next_s();
			tok = indent_block_or_statement(null, true);
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
			// Not seeing an if etc, just loop till we hit our next begin/end/fork/joinetc.]
			if (!parent_is_block)  {
//				enter_scope(tok);
				
				tok = next_s(); // grab the next token, this was probably the first token of a new statement
				// add the indent, so that if the statement runs over multi-lines, we get a bit of an indent here
				start_of_scope (tok);
				enter_scope (tok);
			}
			boolean do_next = true;
			int brace_level = 0;
			while (!tok.isOp(";") || brace_level > 0) {
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
				// Check for and propery indent things that are in brackets
				// for example
				// assign a = (
				//        b + (
				//           (d + e)
				//        )
				//     );
				// Indent on successive (
				if (is_open_brace(tok)) {
					start_of_scope(tok);
					brace_level++;
				// Out-dent on successive )
				} else if (is_close_brace(tok)) {
					leave_scope(tok);
					brace_level--;
				}
				tok = next_s();
			}
			// Un-indent after we indented
			if (!parent_is_block)  {
				leave_scope (tok);
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
			if (tok.isOp("->") || tok.isOp("->>")) {
				tok = next_s();
				tok = indent_constraint_block_or_stmt();
			}
			// Otherwise, really don't know what's being specified
		} else {
			// expression_or_dist ::= expression [ dist { dist_list } ];
			tok = next_skip_over_hier();
			// check if we have a distribution here
			if (tok.isId("dist"))  {
				tok = next_s();			// move onto '{'
				tok = consume_expression();
				tok = next_s();			// consume trailing ;
			}
			// Expression
			else  {
				// Read a statement up to a semi-colon
				while (!tok.isOp(";")) {
					tok = next_s();
				}
				
				tok = next_s();
			}
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
	
	
	/**
	 * This will take a look at the various always... constructs and move through them, 
	 * hopefully working through the rest of the line to either a begin or a statement...
	 * Rules:
	 * always_latch, always_comb : jump straight to parsing statement or block
	 * always, always_ff, or @: make way through the @(...) and then parse statement or block
	 * @return
	 */
	private SVIndentToken indent_always() {
		SVIndentToken tok = current();
//		return (tok.isId("always") || tok.isId("always_comb") ||
//				tok.isId("always_latch") || tok.isId("always_ff"));
		if (tok.isId("always") || (tok.isId("always_ff") || tok.isId("always_latch") || tok.isId("always_comb")))  {
			tok=next_s();	// on always, always_ff this will be an @, otherwise will be begin or start of statement
		}
		// If we have an @, make way to the end of the expression
		if (tok.isOp("@"))  {
			// swallow the expression (...) or @*
			tok = next_s();
			tok=consume_expression();
		}
		// By this point we should have reached a begin or statement
		return (indent_block_or_statement(null, false));
	}
	
	private SVIndentToken indent_case() {
		SVIndentToken tok = current();
		String type = tok.getImage();
		// Synchronize the indent on 'case'
		enter_scope(tok);

		// Push a new scope for the body of the case
		start_of_scope(tok);

		// randcase does not have an expression
		if (is_case(tok)) {
			tok = next_s(); // should be expression
			// Continue on till we get a closed brace.  We could have case (some_vec[3:2]).  
			// This is important because below we just check for : to determine indentation, and
			// a : in the indenter was throwing the indenter off
			if (tok.isOp("("))  {
				while (!next_s().isOp(")")); // should be expression
			}
		}

		tok = next_s();
		
		// Synchronize indent
		enter_scope(tok);
		
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
			set_indent(tok, false, true);
		}
		
		tok = next_s();
		
//		leave_scope();
		
		return tok;
	}
	
	private void start_of_scope(SVIndentToken tok) {
		start_of_scope(tok, true);
	}

	/**
	 * start_of_scope()
	 * 
	 * Called before entry into a new scope. Increases the indent to apply
	 * to any comments between the current token and the first token in the
	 * new scope
	 * @param tok
	 */
	private void start_of_scope(SVIndentToken tok, boolean incr) {
		if (incr) {
			incr_indent(true);
		} else {
			push_indent_stack(peek_indent(), true);
		}
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
			debug("[" + fIndentStack.size() + "] start_of_scope() - indent=\"" + peek_indent() + "\"");
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
	 * In adaptive-indent mode, updates the current indent level
	 * 
	 * @param tok
	 */
	private void enter_scope(SVIndentToken tok) {
		// boolean is_top_scope = (fIndentStack.size() == 1);
		// incr_indent(isAdaptiveTraining(tok));
		
		set_indent(tok, false, true);
		
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
			debug("[" + fIndentStack.size() + "] leave_scope() - indent=\"" + peek_indent() + "\"");
		}
	}
	
	private void push_indent_stack(String indent, boolean provisional) {
		if (fDebugEn) {
			debug("[" + (fIndentStack.size() + 1) + 
					"] push_indent_stack: \"" + indent + "\" provisional=" + provisional);
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
		if (fDebugEn) {
			String img = (tok != null)?tok.getImage():"";
			int level = fIndentStack.size()-1;
			if (level > 0) {
				debug("[" + level + "] pop_indent: \"" + fIndentStack.get(level-1).first() + "\" (" + img + ")");
			} else {
				debug("[" + level + "] pop_indent: (no previous level indent) (" + img + ")");
			}
		}
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
			set_indent(tok, false, true);
		}

		if (fDebugEn) {
			debug("pop_indent - indent=\"" + peek_indent() + "\"");
		}
	}
	
	private void set_indent(SVIndentToken tok, boolean implicit, boolean ok_to_reset_indent) {
		if (tok.isStartLine()) {
			if (ok_to_reset_indent &&
					isAdaptiveTraining(tok) && 
					fIndentStack.peek().second() &&
					!tok.isBlankLine() && !tok.isComment()) {
				// If we are in the training period, the indent
				// level is provisional, and this is not a blank
				// line, then sample the indent
				if (fDebugEn) {
					debug("[" + fIndentStack.size() + "] set_indent: convert implicit indent \"" + 
							fIndentStack.peek().first() + "\" to \"" +
							fCurrentIndent + "\" tok=\"" + tok.getImage() + "\"");
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
			set_indent(tok, false, true);
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
	
	/**
	 * Call this function after begin, or end, endmodule etc. The function will check for a : some_label and consume it and move to the next token
	 * 
	 * Examples
	 * begin : some_label
	 * endmodule : module_name
	 * 
	 * @param tok
	 * @return
	 */
	private SVIndentToken consume_labeled_block(SVIndentToken tok) {
		if (tok.isOp(":")) {
			tok = next_s();		// consume the label
			tok = next_s();		// now move token to the next identifier ... 
		}
		return tok;
	}
	/**
	 * consume_expression
	 * 
	 * This function will parse through an expression such as (a | b)
	 * If a start of line is encountered, subsequent code is indented
	 * The function will return if the end of expression is reached, typically
	 * a matching closing brace is reached.
	 * 
	 * Call this on the following tokens
	 * always @*
	 *         ^ Call on the token after an @
	 * if (...
	 *    ^ Call on the token after an if
	 * 
	 * @return Next Token
	 */
	private SVIndentToken consume_expression() {
		SVIndentToken tok = current();
		boolean is_indent = false;
		boolean search_for_close_brace = false;
		// Get next token
		if (is_open_brace(tok)) {
			tok = next_s();
			search_for_close_brace = true;
			if (tok.isEndLine()) {
				// Should indent (?)
			}
		}
		do {
			// braces on a new line get indented
			if (tok.isStartLine() && (is_indent == false))  {
				is_indent = true;
				start_of_scope(tok);
				enter_scope(tok);
			}
			// If we have an open brace, check if we need to indent, and call this function again to evaluate the expression
			if (is_open_brace(tok)) {
				// recursively call this function, checking for nested braces
				tok = consume_expression();
				// If we come back (will be on a brace, and we had just indented, 
			}
			// Allow for ()
			else if (is_close_brace(tok)) {}
			else  {
				tok = next_s();
			}
		} while (!is_close_brace(tok) && search_for_close_brace);
		
		// If we come back (will be on a brace, and we had just indented, 
		if (is_indent) {
			leave_scope(tok);
		}
		
		if (is_close_brace(tok)) {
			tok = next_s();
		}
		
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
					tok.getType() == SVIndentTokenType.SingleLineComment/* ||
					(tok.isPreProc() && fPreProcDirectives.contains(tok.getImage()))*/)) {
			if (tok.getType() == SVIndentTokenType.SingleLineComment)  {
				set_indent(tok, true, true);
				fTokenList.add(tok);
			} else if (tok.getType() == SVIndentTokenType.MultiLineComment) {
				indent_multi_line_comment(tok);
				fTokenList.add(tok);
// SGD - Removed this because because we want `include, ifdef etc. to match normal code instead of embedding on line 0
// See bug #64 Indenter import `include
//  I have just commented this code out, because I *think* this is where we need to put in `ifdef/`endif indentation
//  in the future.
//			} else if (tok.isPreProc() && !tok.isId("`include")) {
//				// If this is a built-in directive, then place at the
//				// beginning of the line
//				Stack<Tuple<String, Boolean>> stack = fIndentStack;
// 				fIndentStack = new Stack<Tuple<String,Boolean>>();
//				push_indent_stack("", false);
//				set_indent(tok, true);
//				while (tok != null && !tok.isEndLine()) {
//					//fTokenList.add(tok);
//					fTokenList.add(tok);
//					tok = fScanner.next();
//					if (fDebugEn) {
//						debug("pre-proc line: " + ((tok != null)?tok.getImage():"null"));
//					}
//				}
//				
//				if (tok != null) {
//					fTokenList.add(tok);
//				}
//				fIndentStack = stack;
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
				fCurrentIndent = tok.getLeadingNonNewLineWS();
				set_indent(tok, true, true);
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

	/**
	 * This function was written to replace next_s when we are expecting an identifier with a hierarchy in it
	 * for example:
	 * top.bob = ... the function will run past the ., and return bob
	 * 
	 * @return The identifier in the hierarchy 
	 */
	private SVIndentToken next_skip_over_hier () {
		SVIndentToken tok = current();
		tok = next_s();						// get the next id (possibly a hierarchy delimiter '.') 
		while (tok.isOp("."))  {
			tok = next_s();					// identifier
			tok = next_s();					// possible hierarchy delimiter '.'
			// Check for bus values []
			if (tok.isOp("["))  {
				tok = consume_expression();
			}
		}
		return (tok);				// return the last token in hierarchy
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
//			System.out.println("[INDENT] " + msg);
		}
	}
}

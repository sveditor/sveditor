package net.sf.sveditor.core.indent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDefaultIndenter {
	enum State {
		
	};
	private ISVIndentScanner				fScanner;
	private Stack<String>					fIndentStack;
	private List<SVIndentToken>				fTokenList; 
	private int								fTokenIdx;
	private LogHandle						fLog;
	private int								fQualifiers;
	private boolean							fDebugEn = false;
	
	static private Map<String, Integer>		fQualifierMap;

	static {
		fQualifierMap = new HashMap<String, Integer>();
		fQualifierMap.put("static", 	1 << 0);
		fQualifierMap.put("virtual", 	1 << 1);
		fQualifierMap.put("local",		1 << 2);
		fQualifierMap.put("protected",	1 << 3);
		fQualifierMap.put("public",		1 << 4);
		fQualifierMap.put("extern",		1 << 5);
	}
	
	public SVDefaultIndenter() {
		fIndentStack = new Stack<String>();
		fTokenList = new ArrayList<SVIndentToken>();
		fTokenIdx  = -1;
		fLog = LogFactory.getDefault().getLogHandle("SVDefaultIndenter");
	}
	
	public void init(ISVIndentScanner scanner) {
		fScanner = scanner;
		fIndentStack.push("");
	}

	public String indent(int start_line, int end_line) {
		StringBuilder sb = new StringBuilder();
		SVIndentToken 	tok;
		
		while ((tok = fScanner.next()) != null) {
			fTokenList.add(tok);
		}
		
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
							tok.isId("interface") || tok.isId("program")) {
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
					} else {
						tok = next();
					} 
				} while ((tok = current()) != null);
			} catch (RuntimeException e) {
				// e.printStackTrace();
				break;
			}
		}
		
		for (SVIndentToken t : fTokenList) {
			if ((t.getLineno() >= start_line || start_line == -1) &&
					(t.getLineno() <= end_line || end_line == -1)) {
				debug("tok \"" + t.getType() + "\" line=" + t.getLineno() + " image=" + t.getImage());
				sb.append(t.getLeadingWS() + 
						t.getImage() +
						t.getTrailingWS() +
						((t.isEndLine())?"\n":""));
			}
		}
		
		return sb.toString();
	}
	
	private SVIndentToken indent_if() {
		boolean non_block_stmt = false;
		SVIndentToken tok = current();
		debug("--> indent_if() tok=" + tok.getImage());
		
		if ((tok = next()) == null || tok.getType() != SVIndentTokenType.Expression) {
			// bail out -- not sure what happened...
		}
		
		// Advance past expression
		tok = next_s();
		
		if (!tok.isId("begin")) {
			push_indent();
			set_indent(tok);
			non_block_stmt = true;
		}
		
		tok = indent_block_or_statement();
		
		if (non_block_stmt) {
			pop_indent();
			set_indent(tok);
		}
		
		if (tok.isId("else")) {
			tok = next_s();
			if (tok.isId("if")) {
				indent_if();
			} else {
				tok = indent_block_or_statement();
			}
		}
		
		debug("<-- indent_if() tok=" + 
				((tok != null)?tok.getImage():"null"));
		
		return tok;
	}
	
	private SVIndentToken indent_loop_stmt() {
		boolean non_block_stmt = false;
		SVIndentToken tok, first;
		
		tok = first = current();
		debug("--> indent_loop_stmt() tok=" + tok.getImage());
		
		
		if (tok.isId("repeat") || tok.isId("while")) {
			tok = next_s();
			if (tok.getType() != SVIndentTokenType.Expression) {
				return tok;
			}
		}
		
		// Advance past expression
		tok = next_s();
		
		if (!tok.isId("begin")) {
			push_indent();
			set_indent(tok);
			non_block_stmt = true;
		}
		
		tok = indent_block_or_statement();
		
		if (non_block_stmt) {
			pop_indent();
			set_indent(tok);
		}
		
		if (first.isId("do")) {
			// Just read to end of statement
			while (!tok.isOp(";")) {
				next_s();
			}
			tok = next_s();
		}
		
		debug("<-- indent_loop_stmt() tok=" + 
				((tok != null)?tok.getImage():"null"));
		
		return tok;
	}
	
	private SVIndentToken indent_typedef() {
		SVIndentToken tok = current();
		debug("--> indent_typedef()");
		
		tok = next_s();
		
		if (tok.isId("enum") || tok.isId("struct")) {
			while (!tok.isOp("{")) {
				tok = next_s();
			}

			debug("push_indent");
			push_indent();
			
			while (!tok.isOp("}")) {
				tok = next_s();
			}
			debug("pop_indent");
			pop_indent();
			set_indent(tok);
		}

		// read to the end of the statement
		while (!tok.isOp(";")) {
			tok = next_s();
		}
		tok = next_s();
		
		debug("<-- indent_typedef()");
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
		debug("--> indent_ifc_module_class(" + item + ")");
		
		// Reach the end of the declaration
		while (tok != null && !tok.isOp(";")) {
			tok = next_s();
		}
		
		push_indent();
		tok = next_s();
		
		// Now, read body items
		while (tok != null) {
		
			if (tok.isId(end)) {
				break;
			} else if (tok.getType() == SVIndentTokenType.Identifier &&
					fQualifierMap.containsKey(tok.getImage())) {
				tok = next_s();
			} else if (tok.isId("function") || tok.isId("task")) {
				tok = indent_task_function(tok.getImage());
			} else if (tok.isId("covergroup")) {
				tok = indent_covergroup();
			} else {
				tok = indent_block_or_statement();
			}
		}
		
		pop_indent();
		set_indent(tok);
		
		tok = next_s();
		
		debug("--> indent_ifc_module_class(" + item + ") next=" + 
				((tok != null)?tok.getImage():"null"));
		return tok;
	}

	private SVIndentToken indent_covergroup() {
		SVIndentToken tok = current_s();
		debug("--> indent_covergroup()");
		
		// Reach the end of the declaration
		while (tok != null && !tok.isOp(";")) {
			tok = next_s();
		}
		
		push_indent();
		tok = next_s();
		
		// Now, read body items
		while (tok != null) {
		
			if (tok.isId("endgroup")) {
				break;
			} else {
				tok = indent_covergroup_item();
			}
		}
		
		pop_indent();
		set_indent(tok);
		
		tok = next_s();
		
		debug("--> indent_covergroup() next=" +
				((tok != null)?tok.getImage():"null"));
		return tok;
	}
	
	private SVIndentToken indent_covergroup_item() {
		SVIndentToken tok = current();
		
		// Scan to the end of the statement / beginning of the block
		push_indent();
		while (!tok.isOp(";") && !tok.isOp("{")) {
			tok = next_s();
		}
		pop_indent();
		
		if (tok.isOp("{")) {
			int lb_count = 1, rb_count = 0;
			push_indent();
			
			do {
				tok = next_s();
				if (tok.isOp("{")) {
					lb_count++;
				} else if (tok.isOp("}")) {
					rb_count++;
				}
			} while (lb_count != rb_count);
			
			pop_indent();
			set_indent(tok);
		}
		
		tok = next_s();
		
		return tok;
	}

	private SVIndentToken indent_task_function(String item) {
		SVIndentToken tok = current_s();
		String end = get_end_kw(item);
		debug("--> indent_task_function(" + item + ")");
		
		while (tok != null && !tok.isOp(";")) {
			tok = next_s();
		}
		
		// If this is an extern function or task, we're done
		if ((fQualifiers & fQualifierMap.get("extern")) == 0) {
			push_indent();
			tok = next_s();

			while (tok != null) {
				if (tok.isId(end)) {
					break;
				} else {
					tok = indent_block_or_statement();
				}
			}
			pop_indent();
			set_indent(tok);
		}

		tok = next_s();
		
		debug("--> indent_task_function(" + item + ") " +
				((tok != null)?tok.getImage():"null"));
		return tok;
	}
	
	private SVIndentToken indent_block_or_statement() {
		boolean is_block = false;
		SVIndentToken tok = current();
		debug("--> indent_block_or_statement() tok=" + tok.getImage());
		
		if (tok.isId("begin")) {
			is_block = true;
			push_indent();
			
			tok = next_s();
			
			while (tok != null) {
				debug("top of begin/end loop: " + tok.getType() + " " + tok.getImage());
				if (tok.isId("end")) {
					pop_indent();
					set_indent(tok);
					debug("Setting indent \"" + get_indent() + "\"");
					tok = next();
					break;
				} else {
					tok = indent_block_or_statement();
				}
			}
		} else {
			// Just indent the statement
			if (tok.isId("if")) {
				tok = indent_if();
			} else if (tok.isId("case")) {
				tok = indent_case();
			} else if (tok.isId("always")) {
				if ((tok = next_s()).isOp("@")) {
					tok = next_s();
					tok = next_s(); // Should be either stmt or begin
					indent_block_or_statement();
				}
			} else if (tok.isId("typedef")) {
				tok = indent_typedef();
			} else if (tok.isId("while") || tok.isId("do") ||
					tok.isId("repeat") || tok.isId("forever")) {
				tok = indent_loop_stmt();
			} else {
				// Push an indent to handle case where the statement is
				// broken across multiple lines
				// This is a bit of a temporary hack...
				push_indent();
				while (!tok.isOp(";")) {
					tok = next_s();
				}
				pop_indent();
				tok = next_s();
			}
		}

		debug("<-- indent_block_or_statement() tok=" + 
				((tok != null)?tok.getImage():"null") + " is_block=" + is_block);
		
		return tok;
	}
	
	private SVIndentToken indent_case() {
		SVIndentToken tok = current();
		
		System.out.println("indent_case()");
		
		push_indent();
		
		tok = next_s(); // should be expression
		tok = next_s();
		
		while (!tok.isId("endcase")) {
			while (!tok.isOp(":") && !tok.isId("endcase")) {
				tok = next_s();
			}
			
			if (tok.isOp(":")) {
				tok = next_s();
				tok = indent_block_or_statement();
			}
		}
		
		pop_indent();
		if (tok.isId("endcase")) {
			set_indent(tok);
		}
		
		tok = next_s();
		
		return tok;
	}
	
	private void push_indent() {
		fIndentStack.push(fIndentStack.peek() + "\t");
	}
	
	private void pop_indent() {
		if (fIndentStack.size() > 1) {
			fIndentStack.pop();
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
			debug("Multi-line comment is not start-line");
		}
	}
	
	private SVIndentToken next() {
		SVIndentToken tok = null;
		
		// Advance to ensure that current() returns null
		if (fTokenIdx+1 >= fTokenList.size()) {
			fTokenIdx++;
		}
		
		while ((fTokenIdx+1) < fTokenList.size() &&
				(tok = fTokenList.get(++fTokenIdx)) != null &&
				(tok.getType() == SVIndentTokenType.BlankLine ||
					tok.getType() == SVIndentTokenType.MultiLineComment ||
					tok.getType() == SVIndentTokenType.SingleLineComment)) {
			debug("    skipped-next: " + tok.getImage());
			if (tok.getType() == SVIndentTokenType.SingleLineComment) {
				set_indent(tok);
			} else if (tok.getType() == SVIndentTokenType.MultiLineComment) {
				indent_multi_line_comment(tok);
			}
		}
		
		debug("next: tok=" + ((tok != null)?tok.getImage():"null"));
		
		if (tok != null) {
			set_indent(tok);
		}
		
		return tok;
	}
	
	private SVIndentToken current() {
		if (fTokenIdx >= fTokenList.size()) {
			return null;
		}
		
		return fTokenList.get(fTokenIdx);
	}
	
	private SVIndentToken current_s() {
		if (current() == null) {
			throw new RuntimeException();
		}
		
		return current();
	}
	
	private SVIndentToken next_s() {
		SVIndentToken ret = next();
		
		if (ret == null) {
			throw new RuntimeException();
		}
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
		}
	}
	
}

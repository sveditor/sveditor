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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

public class SVIndentParser {
	
	private ISVIndentScanner			fScanner;
	private List<SVIndentToken>			fBuffer;
	private Stack<String>				fIndentStack;
	
	private static final Set<String>	fPreProcKeywords;
	
	
	static {
		fPreProcKeywords = new HashSet<String>();
		fPreProcKeywords.add("`ifdef");
		fPreProcKeywords.add("`ifndef");
		fPreProcKeywords.add("`else");
		fPreProcKeywords.add("`endif");
		fPreProcKeywords.add("`define");
	}
	
	public SVIndentParser(ISVIndentScanner scanner) {
		fScanner 		= scanner;
		fBuffer  		= new ArrayList<SVIndentToken>();
		fIndentStack 	= new Stack<String>();
	}
	
	void indent() {
		while (indent_file()) {
			
		}
	}
	
	private boolean indent_file() {
		SVIndentToken tok;
		
		while ((tok = next()) != null) {
			String id = tok.getImage();
			if (tok.getType() == SVIndentTokenType.Identifier) {
				if (fPreProcKeywords.contains(id)) {
					
				} else if (id.equals("module") || id.equals("interface") ||
						id.equals("class")) {
					
				} else if (id.equals("function") || id.equals("task")) {
					// indent_loop()
				} else {
					// didn't recognize. So, add to the list
					fBuffer.add(tok);
					
				}
			} else if (tok.getType() == SVIndentTokenType.Operator) {
				if (tok.getImage().equals(";")) {
					process_raw_statement(fBuffer);
				} else {
					fBuffer.add(tok);
				}
			}
					
				
		}
		
		return true;
	}
	
	private void process_raw_statement(List<SVIndentToken>	tokens) {
		// Ensure first token is the start of a line
		tokens.get(0).setIsStartLine(true);
		tokens.get(tokens.size()-1).setIsEndLine(true);
		tokens.get(0).setLeadingWS(getIndent());
		
		// Just for now, eliminate any new-lines in the statement
		for (int i=1; i<tokens.size()-1; i++) {
			tokens.get(i).setIsEndLine(false);
			tokens.get(i).setIsStartLine(false);
		}
	}
	
	
	private void indent_behavioral_scope() {
		SVIndentToken tok;
		
		while ((tok = current()) != null) {
			String id = tok.getImage();
			
			if (id.equals("do") || id.equals("while") || 
					id.equals("repeat") || id.equals("forever")) {
				next();
				indent_block_or_stmt();
			} else {
				break;
			}
			next();
		}
	}
	
	private void indent_block_or_stmt() {
		SVIndentToken tok = current();
		
		if (tok.getType() == SVIndentTokenType.Identifier && 
				tok.getImage().equals("begin")) {
			// block
			if (tok.isStartLine()) {
				// ??
			}
			push_indent();
			while ((tok = next()) != null) {
				
				if (tok.getType() == SVIndentTokenType.Identifier &&
						tok.getImage().equals("end")) {
					break;
				} else {
					indent_stmt();
				}
			}
			pop_indent();
		} else {
			// statement
			indent_stmt();
		}
	}
	
	private void indent_stmt() {
		SVIndentToken tok = current();
		
		if (tok.getType() == SVIndentTokenType.Identifier) {
			String id = tok.getImage();
			
			if (id.equals("if")) {
				// indent if / else
				
				// read expression
				
				indent_block_or_stmt();
				
				tok = current();
				if (tok.getType() == SVIndentTokenType.Identifier &&
						tok.getImage().equals("else")) {
					indent_block_or_stmt();
				}
			} else if (id.equals("while") || id.equals("repeat")) {
				// loop statement
			} else if (id.equals("do")) {
				tok = next();
				indent_block_or_stmt();
				if (tok.getImage().equals("while")) {
					
				} else {
					// ERROR
				}
			} else if (id.equals("forever")) {
				indent_block_or_stmt();
			}
		}
	}
	
	private void push_indent() {
		fIndentStack.push(fIndentStack.peek() + "\t");
	}
	
	private void pop_indent() {
		fIndentStack.pop();
	}
	
	private SVIndentToken next() {
		SVIndentToken tok;
		
		while ((tok = fScanner.next()) != null) {
			switch (tok.getType()) {
				case BlankLine:
					break;
				case MultiLineComment:
					break;
				case SingleLineComment:
					break;
				default:
					return tok;
			}
		}
		
		return null;
	}
	
	private SVIndentToken current() {
		return fScanner.current();
	}

	private String getIndent() {
		return fIndentStack.peek();
	}

}

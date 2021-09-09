/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import org.sveditor.core.db.ISVDBAddChildItem;
import org.sveditor.core.db.SVDBItem;

public class SVSpecifyBlockParser extends SVParserBase {
	
	public SVSpecifyBlockParser(ISVParser parser) {
		super(parser);
	}
	
	private static final Set<String> system_timing_checks_kw;
	static {
		system_timing_checks_kw = new HashSet<String>();
		system_timing_checks_kw.add("$setup");
		system_timing_checks_kw.add("$hold");
		system_timing_checks_kw.add("$setuphold");
		system_timing_checks_kw.add("$recovery");
		system_timing_checks_kw.add("$removal");
		system_timing_checks_kw.add("$recrem");
		system_timing_checks_kw.add("$skew");
		system_timing_checks_kw.add("$timeskew");
		system_timing_checks_kw.add("$fullskew");
		system_timing_checks_kw.add("$period");
		system_timing_checks_kw.add("$width");
		system_timing_checks_kw.add("$nochange");
	}

	// TODO: save specify_block info
	public SVDBItem parse(ISVDBAddChildItem parent) throws SVParseException {
		if (fDebugEn) {
			debug("--> specify::parse()");
		}
		fLexer.readKeyword(KW.SPECIFY);
		
		while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDSPECIFY)) {
			if (fDebugEn) {
				debug(" specify item: " + fLexer.peek());
			}
			KW kw;
			if (fLexer.peekKeyword(KW.SPECPARAM)) {
				specparam_declaration(null);
			} else if ((kw = fLexer.peekKeywordE()) != null &&
					(kw == KW.PULSESTYLE_ONEVENT || kw == KW.PULSESTYLE_ONDETECT ||
					 kw == KW.SHOWCANCELLED || kw == KW.NOSHOWCANCELLED)) {
				error("specify-block pulsestyle_onevent, pulsestyle_ondetect, showcancelled, noshowcancelled unsupported");
			} else if (fLexer.peekOperator(OP.LPAREN)) {
				// path_declaration
				path_declaration();

				if (fLexer.peekOperator(OP.EQ)) {
					fLexer.readOperator(OP.EQ);
					list_of_path_delay_expressions();
				}
				fLexer.readOperator(OP.SEMICOLON);
			} else if (fLexer.peekId() && system_timing_checks_kw.contains(fLexer.peek())) {
				system_timing_checks(null);
			} else if (fLexer.peekKeyword(KW.IF, KW.IFNONE)) {
				state_dependent_path_declaration(null);
				fLexer.readOperator(OP.SEMICOLON);
			} else {
				error("Unexpected specify-block item: " + fLexer.peek());
			}
		}
		
		fLexer.readKeyword(KW.ENDSPECIFY);
		
		if (fDebugEn) {
			debug("<-- specify::parse()");
		}
		
		return null;
	}

	// TODO: save data
	public void specparam_declaration(ISVDBAddChildItem parent) throws SVParseException {
		if (fDebugEn) {
			debug("--> specparam_declaration");
		}
		fLexer.readKeyword(KW.SPECPARAM);
		if (fLexer.peekOperator(OP.LBRACKET)) {
			fParsers.dataTypeParser().packed_dim();
		}
	
		while (fLexer.peek() != null) {
			fLexer.readId();
			fLexer.readOperator(OP.EQ);
			fParsers.exprParser().constant_mintypmax_expression();
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		if (fDebugEn) {
			debug("<-- specparam_declaration");
		}
	}
	
	private void system_timing_checks(ISVDBAddChildItem parent) throws SVParseException {
		String type = fLexer.readId();
	
		fLexer.readOperator(OP.LPAREN);
		if (type.equals("$setup") || type.equals("$hold") || 
				type.equals("$recovery") || type.equals("$removal") ||
				type.equals("$skew")) {
			// data_event, reference_event, timing_check_limit [, notifier ]
			timing_check_event(false); // data_event
			fLexer.readOperator(OP.COMMA);
			timing_check_event(false); // reference_event
			fLexer.readOperator(OP.COMMA);
			fParsers.exprParser().expression(); // timing_check_limit
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
				fLexer.readId(); // notifier
			}
		} else if (type.equals("$period")) {
			timing_check_event(true); // data_event
			fLexer.readOperator(OP.COMMA);
			fParsers.exprParser().expression(); // timing_check_limit
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
				fLexer.readId(); // notifier
			}
		} else if (type.equals("$width")) {
			timing_check_event(true); // data_event
			fLexer.readOperator(OP.COMMA);
			fParsers.exprParser().expression(); // timing_check_limit
			
			if (fLexer.peekOperator(OP.COMMA)) {
				// Appears threshold is optional -- at least in Verilog
				fLexer.readOperator(OP.COMMA);
				fParsers.exprParser().expression(); // threshold
			
				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
					fLexer.readId(); // notifier
				}
			}
		} else if (type.equals("$setuphold")) {
			timing_check_event(false); // reference_event
			fLexer.readOperator(OP.COMMA);
			timing_check_event(false); // data_event
			fLexer.readOperator(OP.COMMA);
			fParsers.exprParser().expression(); // timing_check_limit
			fLexer.readOperator(OP.COMMA);
			fParsers.exprParser().expression(); // timing_check_limit
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
				fLexer.readId(); // notifier
			}
			// TODO: 
		} else {
			error("Unsupported system_timing_check " + type);
		}
		fLexer.readOperator(OP.RPAREN);
		fLexer.readOperator(OP.SEMICOLON);
	}

	// TODO: 
	private void timing_check_event(boolean is_controlled) throws SVParseException {
		if (fLexer.peekKeyword(KW.POSEDGE, KW.NEGEDGE)) {
			fLexer.eatToken();
		} else if (fLexer.peekKeyword(KW.EDGE)) {
			// edge [edge_descriptor {, edge_descriptor}]
			// edge 
			fLexer.eatToken();
		
			if (fLexer.peekOperator(OP.LBRACKET)) {
				fLexer.eatToken();
				while (fLexer.peek() != null) {
					// TODO:
					fLexer.eatToken();

					if (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
				fLexer.readOperator(OP.RBRACKET);
			}
		} else if (is_controlled) {
			error("Expecting posedge, negedge, edge");
		}
	
		// <id> | <id>.<id>
		fLexer.readId();
		if (fLexer.peekOperator(OP.DOT)) {
			fLexer.eatToken();
			fLexer.readId();
		}
		
		if (fLexer.peekOperator(OP.LBRACKET)) {
			fLexer.eatToken();
			fParsers.exprParser().const_or_range_expression();
			fLexer.readOperator(OP.RBRACKET);
		}
		
		if (fLexer.peekOperator(OP.AND3)) {
			fLexer.eatToken();
			// timing_check_condition
			// TODO: incomplete
			fParsers.exprParser().expression();
		}
	}

	// TODO: store data
	private void path_declaration() throws SVParseException {
		int count=0;
	
		if (fDebugEn) {
			debug("--> path_declaration " + fLexer.peek());
		}
		
		fLexer.readOperator(OP.LPAREN);
		while (fLexer.peek()  != null) {
			if (fDebugEn) {
				debug("  loop1: " + fLexer.peek());
			}
			if (fLexer.peekKeyword(KW.POSEDGE, KW.NEGEDGE, KW.EDGE)) {
				// TODO: save
				fLexer.eatToken();
			}
			specify_inout_terminal_descriptor();
			count++;
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
	
		if (fDebugEn) {
			debug("  count: " + count + " " + fLexer.peek());
		}
		if (count > 1) {
			fLexer.readOperator(OP.MUL_GT, OP.SUB_MUL_GT, OP.PLUS_MUL_GT);
		} else {
			// Single start point, one or many end-points
			if (fLexer.peekOperator(OP.EQ_GT, OP.SUB_GE, OP.PLUS_GE, OP.MUL_GT, OP.SUB_MUL_GT, OP.PLUS_MUL_GT)) {
				fLexer.eatToken();
			}
		}
		
		// output-terminal descriptors
		boolean output_paren = fLexer.peekOperator(OP.LPAREN);
		if (output_paren) {
			fLexer.eatToken();
		}
		
		while (fLexer.peek()  != null) {
			if (fDebugEn) {
				debug("  loop2: " + fLexer.peek());
			}
			specify_inout_terminal_descriptor();
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
//		if (output_paren) {
//			if (fLexer.peekOperator("-", "+")) {
//				// TODO: save
//				fLexer.eatToken();
//			}
//		
////			fLexer.readOperator(OP.COLON);
//			// data_source_expression
//			// TODO: save expression
//			fParsers.exprParser().expression();
//		}
		
		if (output_paren) {
			fLexer.readOperator(OP.RPAREN);
		}
		
		fLexer.readOperator(OP.RPAREN);
		
		fLexer.readOperator(OP.EQ);
		fParsers.exprParser().path_delay_value();
		
		if (fDebugEn) {
			debug("<-- path_declaration " + fLexer.peek());
		}
	}
	
	private void specify_inout_terminal_descriptor() throws SVParseException {
		boolean loop_while_in_range = true;
		if (fDebugEn) {
			debug("--> specify_inout_terminal_descriptor " + fLexer.peek());
		}
		while (loop_while_in_range)  {
			fLexer.readId();
			
			if (fLexer.peekOperator(OP.LBRACKET)) {
				fLexer.eatToken();
				fParsers.exprParser().const_or_range_expression();
				fLexer.readOperator(OP.RBRACKET);
			}
			// Check for const_indexed_range operators
			if (!fLexer.peekOperator(OP.COLON, OP.PLUS_COLON, OP.SUB_COLON)) {
				loop_while_in_range = false;
			}
			else  {
				fLexer.readOperator(OP.COLON, OP.PLUS_COLON, OP.SUB_COLON);
			}
		}
		if (fDebugEn) {
			debug("<-- specify_inout_terminal_descriptor " + fLexer.peek());
		}
	}
	
	private void list_of_path_delay_expressions() throws SVParseException {
		boolean has_paren = fLexer.peekOperator(OP.LPAREN);
		int path_delay_count = 0;
		
		if (has_paren) {
			fLexer.readOperator(OP.LPAREN);
		}
	
		while (fLexer.peek() != null) {
			fLexer.readNumber();
			path_delay_count++;
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		// Expect 1, 2, 3, 6, or 12
	
		if (has_paren) {
			fLexer.readOperator(OP.RPAREN);
		}
	}

	// TODO: save data
	private void state_dependent_path_declaration(ISVDBAddChildItem parent) throws SVParseException {
		if (fDebugEn) {
			debug("--> state_dependent_path_declaration " + fLexer.peek());
		}
		if (fLexer.peekKeyword(KW.IF)) {
			fLexer.eatToken();
			fLexer.readOperator(OP.LPAREN);
			fParsers.exprParser().module_path_expression();
			fLexer.readOperator(OP.RPAREN);
			
			// simple_path_declaration | edge_sensitive_path_declaration
			path_declaration();
		} else {
			// ifnone
//			fParsers.exprParser().simple_path_expression();
			error("ifnone unsupported");
		}
		
		if (fDebugEn) {
			debug("<-- state_dependent_path_declaration " + fLexer.peek());
		}
	}
}

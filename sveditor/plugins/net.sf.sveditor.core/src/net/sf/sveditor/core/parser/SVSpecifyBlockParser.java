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

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBItem;

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
		fLexer.readKeyword("specify");
		
		while (fLexer.peek() != null && !fLexer.peekKeyword("endspecify")) {
			if (fLexer.peekKeyword("specparam")) {
				specparam_declaration(null);
			} else if (fLexer.peekKeyword("pulsestyle_onevent", "pulsestyle_ondetect",
					"showcancelled", "noshowcancelled")) {
				error("specify-block pulsestyle_onevent, pulsestyle_ondetect, showcancelled, noshowcancelled unsupported");
			} else if (fLexer.peekOperator("(")) {
				// path_declaration
				path_declaration();
				
				fLexer.readOperator("=");
				list_of_path_delay_expressions();
				fLexer.readOperator(";");
			} else if (fLexer.peekId() && system_timing_checks_kw.contains(fLexer.peek())) {
				system_timing_checks(null);
			} else if (fLexer.peekKeyword("if","ifnone")) {
				state_dependent_path_declaration(null);
			} else {
				error("Unexpected specify-block item: " + fLexer.peek());
			}
		}
		
		fLexer.readKeyword("endspecify");
		
		return null;
	}

	// TODO: save data
	public void specparam_declaration(ISVDBAddChildItem parent) throws SVParseException {
		fLexer.readKeyword("specparam");
		if (fLexer.peekOperator("[")) {
			fParsers.dataTypeParser().packed_dim();
		}
	
		while (fLexer.peek() != null) {
			fLexer.readId();
			fLexer.readOperator("=");
			fParsers.exprParser().constant_mintypmax_expression();
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		fLexer.readOperator(";");
	}
	
	private void system_timing_checks(ISVDBAddChildItem parent) throws SVParseException {
		String type = fLexer.readId();
	
		fLexer.readOperator("(");
		if (type.equals("$setup") || type.equals("$hold") || 
				type.equals("$recovery") || type.equals("$removal") ||
				type.equals("$skew")) {
			// data_event, reference_event, timing_check_limit [, notifier ]
			timing_check_event(false); // data_event
			fLexer.readOperator(",");
			timing_check_event(false); // reference_event
			fLexer.readOperator(",");
			fParsers.exprParser().expression(); // timing_check_limit
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				fLexer.readId(); // notifier
			}
		} else if (type.equals("$period")) {
			timing_check_event(true); // data_event
			fLexer.readOperator(",");
			fParsers.exprParser().expression(); // timing_check_limit
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				fLexer.readId(); // notifier
			}
		} else if (type.equals("$width")) {
			timing_check_event(true); // data_event
			fLexer.readOperator(",");
			fParsers.exprParser().expression(); // timing_check_limit
			
			if (fLexer.peekOperator(",")) {
				// Appears threshold is optional -- at least in Verilog
				fLexer.readOperator(",");
				fParsers.exprParser().expression(); // threshold
			
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					fLexer.readId(); // notifier
				}
			}
		} else if (type.equals("$setuphold")) {
			timing_check_event(false); // reference_event
			fLexer.readOperator(",");
			timing_check_event(false); // data_event
			fLexer.readOperator(",");
			fParsers.exprParser().expression(); // timing_check_limit
			fLexer.readOperator(",");
			fParsers.exprParser().expression(); // timing_check_limit
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				fLexer.readId(); // notifier
			}
			// TODO: 
		} else {
			error("Unsupported system_timing_check " + type);
		}
		fLexer.readOperator(")");
		fLexer.readOperator(";");
	}

	// TODO: 
	private void timing_check_event(boolean is_controlled) throws SVParseException {
		if (fLexer.peekKeyword("posedge", "negedge")) {
			fLexer.eatToken();
		} else if (fLexer.peekKeyword("edge")) {
			// edge [edge_descriptor {, edge_descriptor}]
			// edge 
			fLexer.eatToken();
		
			if (fLexer.peekOperator("[")) {
				fLexer.readOperator("[");
				while (fLexer.peek() != null) {
					// TODO:
					fLexer.eatToken();

					if (fLexer.peekOperator(",")) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
				fLexer.readOperator("]");
			}
		} else if (is_controlled) {
			error("Expecting posedge, negedge, edge");
		}
	
		// <id> | <id>.<id>
		fLexer.readId();
		if (fLexer.peekOperator(".")) {
			fLexer.eatToken();
			fLexer.readId();
		}
		
		if (fLexer.peekOperator("[")) {
			fLexer.readOperator("[");
			fParsers.exprParser().const_or_range_expression();
			fLexer.readOperator("]");
		}
		
		if (fLexer.peekOperator("&&&")) {
			fLexer.eatToken();
			// timing_check_condition
			// TODO: incomplete
			fParsers.exprParser().expression();
		}
	}

	// TODO: store data
	private void path_declaration() throws SVParseException {
		int count=0;
		
		fLexer.readOperator("(");
		while (fLexer.peek()  != null) {
			specify_inout_terminal_descriptor();
			count++;
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		if (count > 1) {
			fLexer.readOperator("*>");
		} else {
			fLexer.readOperator("=>");
		}
		
		// output-terminal descriptors
		while (fLexer.peek()  != null) {
			specify_inout_terminal_descriptor();
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		fLexer.readOperator(")");
	}
	
	private void specify_inout_terminal_descriptor() throws SVParseException {
		fLexer.readId();
		
		if (fLexer.peekOperator("[")) {
			fLexer.eatToken();
			fParsers.exprParser().const_or_range_expression();
			fLexer.readOperator("]");
		}
	}
	
	private void list_of_path_delay_expressions() throws SVParseException {
		boolean has_paren = fLexer.peekOperator("(");
		int path_delay_count = 0;
		
		if (has_paren) {
			fLexer.readOperator("(");
		}
	
		while (fLexer.peek() != null) {
			fLexer.readNumber();
			path_delay_count++;
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		// Expect 1, 2, 3, 6, or 12
	
		if (has_paren) {
			fLexer.readOperator(")");
		}
	}

	// TODO: save data
	private void state_dependent_path_declaration(ISVDBAddChildItem parent) throws SVParseException {
		if (fLexer.peekKeyword("if")) {
			fLexer.eatToken();
			fLexer.readOperator("(");
			fParsers.exprParser().module_path_expression();
			fLexer.readOperator(")");
		} else {
			// ifnone
//			fParsers.exprParser().simple_path_expression();
			error("ifnone unsupported");
		}
		
	}
}

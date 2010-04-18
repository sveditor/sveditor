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

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import net.sf.sveditor.core.parser.SVToken_sav.Type;

/**
 * Parses a SystemVerilog description. The structure is based on Annex A 
 * (Formal syntax) of IEEE 1800-2005 (SystemVerilog Standard)  
 * 
 * @author ballance
 */
public class SystemVerilogParser_sav {
	private SVLexer_sav				fLexer;
	private int					fLifetimeFlags;
	private int					fClassItemQualifier;
	
	public SystemVerilogParser_sav(SVLexer_sav lex) {
		fLexer = lex;
	}
	
	/**
	 * 
	 */
	public void parse() {
		SVToken_sav tok = next_token_ignore_attr();
		
		while (tok != null) {
			if (tok.isKeyword("class")) {
				System.out.println("class");
				tok = class_declaration(tok);
			} else {
				tok = next_token_ignore_attr();
			}
		}
	}
	
	/**
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav timeunits_declaration(SVToken_sav tok) {
		// TODO:
		
		return tok;
	}
	
	/**
	 * Processes zero or more  
	 * @param tok
	 * @return
	 */
	private SVToken_sav description(SVToken_sav tok) {
		/*
		while (true) {
			// handle attributes that may be attached to this description
		
			if (tok.getType() == Type.Keyword) {
				if (kw == SVKeywords.KW_module || kw == SVKeywords.KW_macromodule) {
					tok = module_declaration(tok);
				} else if (kw == SVKeywords.KW_class || kw == SVKeywords.KW_virtual) {
					tok = class_declaration(tok);
				} else {
				}
			} else {
				// Unknown
				break;
			}
		}
			*/
		
		return tok;
	}
	
	/**
	 * Process module declaration
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav module_declaration(SVToken_sav tok) {
		/*
		assert tok.getKeyword() == SVKeywords.KW_module || 
			tok.getKeyword() == SVKeywords.KW_macromodule;
		 */
		
		tok = next_token_ignore_attr();
		
		/*
		if (tok.getKeyword() == SVKeywords.KW_extern) {
			// TODO: add extern to some flag list
			tok = next_token_ignore_attr();
		}
		 */
		
		// allow specification of lifetime
		tok = lifetime(tok);
		
		tok = expect_next_type(SVToken_sav.Type.Id);
		SVToken_sav name = tok;
		
		/**
		 * Allow module in-line parameter declaration 
		 */
		tok = next_token_ignore_attr();
		if (tok.getType() == Type.Hash) {
			tok = parameter_port_list(tok);
		}
		
		/**
		 * Parse a port-list if the next token is '('
		 */
		if (tok.getType() == Type.LParen) {
			list_of_ports(tok);
		}
		
		expect_type(tok, Type.Semicolon);
		
		// Ensure that we have proper termination of the module declaration

		// assert tok.getKeyword() == SVKeywords.KW_endmodule;
		
		tok = next_token_ignore_attr();
		
		return tok;
	}
	
	private SVToken_sav class_declaration(SVToken_sav tok) {
		/*
		if (tok.getKeyword() == SVKeywords.KW_virtual) {
			tok = next_token_ignore_attr();
		}
		
		if (tok.getKeyword() != SVKeywords.KW_class) {
			System.out.println("[ERROR] expecting 'class'");
		}
		
		// lifetime
		tok = lifetime(tok);

		SVToken class_identifier = expect_next_type(Type.Id);

		tok = next_token_ignore_attr();
		
		if (tok.getType() == Type.LParen) {
			tok = parameter_port_list(tok);
		}
		
		if (tok.getKeyword() == SVKeywords.KW_extends) {
			SVToken extends_type = expect_next_type(Type.Id);
			
			tok = next_token_ignore_attr();
			
			if (tok.getType() == Type.LParen) {
				tok = list_of_arguments(tok);
			}
		}
		
		// terminating semi-colon of the class declaration line
		expect_type(tok, Type.Semicolon);
		
		tok = next_token_ignore_attr();
		while (tok != null && isClassItemStart(tok)) {
			// Process class_item
			if (isMethodQualifier(tok)) {
				tok = method_qualifier(tok);
			} else if (isClassMethodStart(tok)) {
				class_method(tok);
			}
		}
		
		if (tok == null || tok.getKeyword() != SVKeywords.KW_endclass) {
			System.out.println("[ERROR] unterminated class");
		}
		
		tok = next_token_ignore_attr();
		
		if (tok != null && tok.getType() == Type.Colon) {
			tok = next_token_ignore_attr(); // class_identifier
			
			tok = next_token_ignore_attr(); // true next token
		}
		 */
		
		return tok;
	}
	
	
	private SVToken_sav list_of_arguments(SVToken_sav tok) {
		// TODO:
		return tok;
	}

	/**
	 * Checks whether 'tok' is the beginning of a class item
	 *  
	 * @param tok
	 * @return
	 */
	private boolean isClassItemStart(SVToken_sav tok) {
		boolean ret = false;
		
		/*
		
		ret |= isClassItemQualifier(tok);
		ret |= isMethodQualifier(tok);
		
		ret |= (tok.getKeyword() == SVKeywords.KW_task ||
				tok.getKeyword() == SVKeywords.KW_function);
				
				*/
		
		return false;
	}
	
	private boolean isClassItemQualifier(SVToken_sav tok) {
		return false;
		/*
		return (tok.getKeyword() == SVKeywords.KW_static ||
				tok.getKeyword() == SVKeywords.KW_protected ||
				tok.getKeyword() == SVKeywords.KW_local);
		 */
	}
	
	private boolean isMethodQualifier(SVToken_sav tok) {
		return false;
		
		/*
		return (tok.getKeyword() == SVKeywords.KW_virtual ||
				isClassItemQualifier(tok));
		 */
	}
	
	private SVToken_sav method_qualifier(SVToken_sav tok) {
		fClassItemQualifier = 0;
		
		while (isMethodQualifier(tok)) {
			// TODO: aggregate qualifiers
			tok = next_token_ignore_attr();
		}
		
		return tok;
	}

	private SVToken_sav class_item_qualifier(SVToken_sav tok) {
		fClassItemQualifier = 0;
		
		while (isClassItemQualifier(tok)) {
			// TODO: aggregate qualifiers
			tok = next_token_ignore_attr();
		}
		
		return tok;
	}
	
	private boolean isClassMethodStart(SVToken_sav tok) {
		return false;
		/*
		return (tok.getKeyword() == SVKeywords.KW_extern ||
				tok.getKeyword() == SVKeywords.KW_function ||
				tok.getKeyword() == SVKeywords.KW_task ||
				tok.getKeyword() == SVKeywords.KW_extern);
		 */
	}
	
	private SVToken_sav class_method(SVToken_sav tok) {
		boolean extern = false;
		
		/*
		if (tok.getKeyword() == SVKeywords.KW_extern) {
			extern = true;
			tok = next_token_ignore_attr();
		}
		
		tok = method_qualifier(tok);
		
		
		if (tok.getKeyword() == SVKeywords.KW_function) {
			// TODO: if extern
			
			// could be either a function or a constructor
			tok = next_token_ignore_attr();
		}
		 */
		
		return tok;
	}
	
	private SVToken_sav task_declaration(SVToken_sav tok) {
		
		// TODO:
		
		return tok;
	}
	
	/**
	 * Parses a function declaration. 'tok' is expected to be 'function'
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav function_declaration(SVToken_sav tok) {
		boolean ansi_style_decl = false;
		
		tok = next_token_ignore_attr();
		tok = lifetime(tok);
		
		// function_body_declaration
		// -> function_data_type_or_implicit
		// -> TODO: handle signed types (?)
	
		// ->function_data_type
		/*
		if (tok.getKeyword() != SVKeywords.KW_void) {
			tok = data_type(tok);
		}
		 */
		
		// [ interface_identifier '.' | class_scope ]
		
		// function_identifier
		SVToken_sav function_identifier = tok;
		
		tok = next_token();
		
		// ANSI-style prototype
		if (tok.getType().equals(SVToken_sav.Type.LParen)) {
			tok = tf_port_list(tok);
			ansi_style_decl = true;
		}
		
		tok = expect_next_type(SVToken_sav.Type.Semicolon);
		tok = next_token_ignore_attr();
		
		// non-ANSI-style parameter declarations
		if (!ansi_style_decl) {
			tok = tf_item_declaration(tok);
		}
		
		while (tok != null && isTFStatement(tok)) {
	
			tok = next_token_ignore_attr();
		}
		
		
		return tok;
	}
	
	private boolean isTFStatement(SVToken_sav tok) {
		// TODO:
		return false;
	}
	
	/**
	 * Parses a dpi_import_export. Expects tok to be 'export' or 'import'
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav dpi_import_export(SVToken_sav tok) {
		SVToken_sav import_export = tok;
		SVToken_sav task_or_function = null;
		
		tok = expect_next_type(SVToken_sav.Type.String);
		
		if (!tok.getImage().equals("DPI-C") && !tok.getImage().equals("DPI")) {
			System.out.println("[ERROR] expecting \"DPI-C\" or \"DPI\"");
		}
		
		tok = next_token();
		
		/*
		if (import_export.getKeyword() == SVKeywords.KW_import) {
			SVToken import_property;
			
			// dpi_function_import_property | dpi_task_import_property
			
			if (tok.getKeyword() == SVKeywords.KW_context ||
					tok.getKeyword() == SVKeywords.KW_pure) {
				import_property = tok;
				tok = next_token();
			}
			
			if (tok.getType() == Type.Id) {
				// c_identifier
				expect_next_type(Type.Equals);
				tok = next_token();
			}
			
			task_or_function = tok;
			
			if (tok.getKeyword() == SVKeywords.KW_task) {
				tok = task_prototype(tok);
			} else if (tok.getKeyword() != SVKeywords.KW_function) {
				tok = function_prototype(tok);
			} else {
				System.out.println("[ERROR] expecting task or function");
			}
			
			expect_type(tok, Type.Semicolon);
		} else {
			SVToken task_func_identifier;
			
			// optional c_identifier
			if (tok.getType() == Type.Id) {
				tok = expect_next_type(SVToken.Type.Equals);
				tok = next_token();
			}
			
			task_or_function = tok;
			
			if (tok.getKeyword() != SVKeywords.KW_task && 
					tok.getKeyword() != SVKeywords.KW_function) {
				System.out.println("[ERROR] expect 'task' or 'function'");
			}
			
			task_func_identifier = expect_next_type(Type.Id);

			expect_next_type(Type.Semicolon);
		}
		 */
		
		tok = next_token();
		
		return tok;
	}
	
	/**
	 * On entry, expect 'tok' == 'task'
	 * @param tok
	 * @return
	 */
	private SVToken_sav task_prototype(SVToken_sav tok) {
		
		SVToken_sav task_identifier = tok = expect_next_type(Type.Id);
		
		tok = expect_next_type(Type.LParen);
		
		tok = next_token();
		
		tok = tf_port_list(tok);
		
		expect_type(tok, Type.RParen);
		
		tok = next_token();
		
		return tok;
	}
	
	/**
	 * On entry, expect 'tok' == "function"
	 * 
	 */
	private SVToken_sav function_prototype(SVToken_sav tok) {
		
		tok = next_token_ignore_attr();
		
		tok = function_data_type(tok);
		
		expect_type(tok, Type.Id);
		SVToken_sav function_id = tok;
		
		tok = expect_next_type(Type.LParen);
		
		tok = tf_port_list(tok);
		
		expect_type(tok, Type.RParen);
		
		tok = next_token();
		
		return tok;
	}
	
	private SVToken_sav function_data_type(SVToken_sav tok) {
		/*
		if (tok.getKeyword() == SVKeywords.KW_void) {
			tok = next_token();
		} else {
			tok = data_type(tok);
		}
		 */
		
		return tok;
	}
	
	/**
	 * Parse an argument list.
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav tf_port_list(SVToken_sav tok) {

		if (tok.getType() != Type.RParen) {
			// assume we have items
			while (true) {
				tok = tf_port_item(tok);
				
				if (tok.getType() != Type.Comma) {
					// hopefully, this is a RParen
					break;
				}
			}
		}
		
		return tok;
	}
	
	private SVToken_sav tf_port_item(SVToken_sav tok) {
		SVToken_sav param_name = null;
		if (isTFPortDirection(tok)) {
			tok = next_token();
		}
		
		// FIXME: For now, just scan ahead until we hit a comma, 
		//        RParen, semi-colon, or EOF
		while (tok != null && tok.getType() != Type.RParen &&
				tok.getType() != Type.Comma && tok.getType() != Type.Semicolon) {
			param_name = tok;
			tok = next_token_ignore_attr();
		}
		
		expect_type(param_name, Type.Id);
		
		return tok;
	}

	/*
	private SVToken data_type_or_implicit(SVToken tok) {
		if (is_data_type(tok)) {
			
		} else {
			// expect implicit with possible packed dimension
		}
	}
	 */

	/**
	 * [input|output|inout]
	 * [var]
	 * 
	 * @param tok
	 * @return
	 */
/*	
	private boolean isTFPortItemStart(SVToken tok) {
		return (tok.getKeyword() == SVKeywords.)
	}
	 */
	
	private boolean isTFPortDirection(SVToken_sav tok) {
		/*
		return (tok.getKeyword() == SVKeywords.KW_input ||
				tok.getKeyword() == SVKeywords.KW_output ||
				tok.getKeyword() == SVKeywords.KW_inout);
		 */
		return false;
	}
	
	private SVToken_sav tf_item_declaration(SVToken_sav tok) {
		return tok;
	}
	
	/**
	 * data_type ::=
     *   integer_vector_type [ signing ] { packed_dimension }
     * | integer_atom_type [ signing ]
     * | non_integer_type
     * | struct_union [ packed [ signing ] ] { struct_union_member { struct_union_member } }
     * { packed_dimension }12
     * | enum [ enum_base_type ] { enum_name_declaration { , enum_name_declaration } }
     * | string
     * | chandle
     * | virtual [ interface ] interface_identifier
     * | [ class_scope | package_scope ] type_identifier { packed_dimension }
     * | class_type
     * | event
     * | ps_covergroup_identifier
     * | type_reference
     * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav data_type(SVToken_sav tok) {
		// TODO:
		return tok;
	}
	
	/**
	 * parameter_port_list
	 * 
	 * Assumes entry token is '#'
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav parameter_port_list(SVToken_sav tok) {
		tok = expect_next_type(Type.LParen);
		
		// TODO:
		
		return tok;
	}
	
	/**
	 *
	 * Expects 'tok' to be LParen
	 * @param tok
	 * @return
	 */
	private SVToken_sav list_of_ports(SVToken_sav tok) {
		expect_type(tok, Type.LParen);
		
		do {
			tok = next_token_ignore_attr();
			
			// Allow empty list_of_ports
			if (tok.getType() != Type.RParen) {
				tok = port(tok);
			}
		} while (tok.getType() == Type.Comma);
		
		// expect final token to be closing paren
		expect_next_type(Type.RParen);
		tok = next_token_ignore_attr();
		
		return tok;
	}
	
	/**
	 * parses a port. Entry pre-condition is a non-empty port expression
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav port(SVToken_sav tok) {
		if (tok.getType() == Type.Period) {
			// port_identifier '(' optional_port_expression ')'
		} else {
			// 
		}
		
		return tok;
	}
	
	/**
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav lifetime(SVToken_sav tok) {
		fLifetimeFlags = 0;
		
		/*
		if (tok.getKeyword() == SVKeywords.KW_static) {
			tok = next_token_ignore_attr();
		} else if (tok.getKeyword() == SVKeywords.KW_automatic) {
			tok = next_token_ignore_attr();
		}
		 */
		
		return tok;
	}

	/**
	 * Scans zero or more attribute instances
	 * 
	 * @param tok
	 * @return
	 */
	private SVToken_sav attribute_instance(SVToken_sav tok) {
		// TODO:
		
		return tok;
	}
	
	/**
	 * Fetch the next token and check that its type is 'type'
	 */
	private SVToken_sav expect_next_type(SVToken_sav.Type type) {
		SVToken_sav ret = next_token_ignore_attr();
		
		if (ret.getType() != type) {
			System.out.println("[ERROR] expect type " + type + " ; receive " +
					ret.getType() + " instead");
		}
		
		return ret;
	}
	
	private void expect_type(SVToken_sav tok, SVToken_sav.Type ... types) {
		boolean match = false;
		
		for (SVToken_sav.Type t : types) {
			if (tok.getType() == t) {
				match = true;
				break;
			}
		}
		
		if (!match) {
			String types_s = "";
			
			for (SVToken_sav.Type t : types) {
				types_s += t.name() + ", ";
			}
			
			if (types_s.endsWith(", ")) {
				types_s = types_s.substring(0, types_s.length()-2);
			}
			
			System.out.println("[ERROR] expect one of types \"" + types_s + 
					"\" ; receive " + tok.getType() + " instead");
		}
	}
	
	private SVToken_sav next_token_ignore_attr() {
		SVToken_sav tok = next_token();
		
		return attribute_instance(tok);
	}
	
	private SVToken_sav next_token() {
		SVToken_sav ret = fLexer.next_token();
		
		if (ret != null) {
			System.out.println("tok: \"" + ret.getImage() + "\"");
		} else {
			System.out.println("EOF");
		}
		
		return ret;
	}
	
	
	public static final void main(String args[]) {
		
		for (String arg : args) {
			try {
				InputStream in = new FileInputStream(arg);
				SVLexer_sav lex = new SVLexer_sav(new SVInputStream_sav(in));
				SystemVerilogParser_sav p = new SystemVerilogParser_sav(lex);
				p.parse();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

}

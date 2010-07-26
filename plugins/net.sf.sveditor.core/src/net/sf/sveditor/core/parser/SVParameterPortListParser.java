package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class SVParameterPortListParser extends SVParserBase {
	
	public SVParameterPortListParser(ISVParser parser) {
		super(parser);
	}
	
	/**
	 * parameter_port_list ::=
	 * 	# ( list_of_param_assignments { , parameter_port_declaration } )
	 * 	| # ( parameter_port_declaration { , parameter_port_declaration } )
	 * 	| #( )
	 * 
	 * @return
	 * @throws SVParseException
	 */
	public List<SVDBModIfcClassParam> parse() throws SVParseException {
		List<SVDBModIfcClassParam> params = new ArrayList<SVDBModIfcClassParam>();
		
		lexer().readOperator("#");
		lexer().readOperator("(");
		
		while (!lexer().peekOperator(")")) {
			String id = null;
			SVDBModIfcClassParam p;

			// Parameter can be typed or untyped
			// type T=int
			// string Ts="foo"
			// parameter int c[1:0]
			if (lexer().peekKeyword("type")) {
				lexer().eatToken();
				id = lexer().readIdOrKeyword();
			} else {
				if (lexer().peekKeyword("parameter")) {
					lexer().eatToken();
				}
				// This might be a type
				SVDBTypeInfo type = parsers().dataTypeParser().data_type(0, lexer().eatToken());

				// If the next element is an operator, then the 
				// return from the type parser is the parameter name
				if (lexer().peekOperator(",", ")", "=")) {
					id = type.getName();
				} else {
					// Otherwise, we have a type and a parameter name
					id = lexer().readIdOrKeyword();
				}
			}
			
			if (lexer().peekOperator("[")) {
				// TODO: handle vectored
				lexer().skipPastMatch("[", "]");
			}
			
			// id now holds the template identifier
			p = new SVDBModIfcClassParam(id);

			if (lexer().peekOperator("=")) {
				lexer().eatToken();
				
				id = parsers().SVParser().readExpression();
				p.setDefault(id);
			}

			params.add(p);

			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			} else {
				break;
			}
		}
		lexer().readOperator(")");
		
		
		return params;
	}

}

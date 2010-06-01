package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassParam;
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
		
		/*
		lexer().startCapture();
		lexer().skipPastMatch("(", ")");
		String param_s = lexer().endCapture();
		
		ITextScanner in = new StringTextScanner(new StringBuilder(param_s));
		 */
		String id;
		
		/*
		ch = in.skipWhite(in.get_ch());
		if (ch != '(') {
			in.unget_ch(ch);
		}
		 */

		while (true) {
			SVDBModIfcClassParam p;

			if (lexer().peekKeyword("type")) {
				lexer().eatToken();
			}
			id = lexer().readId();

			// id now holds the template identifier
			p = new SVDBModIfcClassParam(id);

			/* ??
			ch = in.skipWhite(in.get_ch());

			if (ch == '(') {
				ch = in.skipPastMatch("()");
			}

			ch = in.skipWhite(ch);
			 */
			
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

package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassParam;

public class SVParameterDeclParser extends SVParserBase {
	private SVExprParser				fExprParser;
	
	public SVParameterDeclParser(ISVParser parser) {
		super(parser);
		fExprParser			= new SVExprParser(parser);
	}
	
	public List<SVDBModIfcClassParam> parse() throws SVParseException {
		List<SVDBModIfcClassParam> param_l = new ArrayList<SVDBModIfcClassParam>();
		lexer().readOperator("(");
		
		while (lexer().peekKeyword("type") || lexer().peekId()) {
			if (lexer().peekKeyword("type")) {
				// TODO: recognize parameters as typed
				lexer().eatToken();
			}
			SVDBModIfcClassParam p = new SVDBModIfcClassParam(lexer().getImage());
			
			// TODO: {unpacked dimension}
			
			lexer().readOperator("=");
			
			
		}
		
		return param_l;
	}
}

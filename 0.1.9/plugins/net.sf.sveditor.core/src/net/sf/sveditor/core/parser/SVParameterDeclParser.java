package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassParam;

public class SVParameterDeclParser extends SVParserBase {
	private SVExprParser				fExprParser;
	
	public SVParameterDeclParser(SVLexer lexer) {
		super(lexer);
		fExprParser			= new SVExprParser(lexer);
	}
	
	public List<SVDBModIfcClassParam> parse() throws SVParseException {
		List<SVDBModIfcClassParam> param_l = new ArrayList<SVDBModIfcClassParam>();
		fLexer.readOperator("(");
		
		while (fLexer.peekKeyword("type") || fLexer.peekId()) {
			if (fLexer.peekKeyword("type")) {
				// TODO: recognize parameters as typed
				fLexer.eatToken();
			}
			SVDBModIfcClassParam p = new SVDBModIfcClassParam(fLexer.getImage());
			
			// TODO: {unpacked dimension}
			
			fLexer.readOperator("=");
			
			
		}
		
		return param_l;
	}
}

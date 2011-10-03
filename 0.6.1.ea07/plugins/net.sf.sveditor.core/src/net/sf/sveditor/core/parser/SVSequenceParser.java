package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBSequence;

public class SVSequenceParser extends SVParserBase {
	
	public SVSequenceParser(ISVParser parser) {
		super(parser);
	}
	
	public void sequence(ISVDBAddChildItem parent) throws SVParseException {
		SVDBSequence seq = new SVDBSequence();
		seq.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("sequence");
		
		seq.setName(fLexer.readId());
		
		if (fLexer.peekOperator("(")) {
			// TODO: sequence_port_list
		}
		fLexer.readOperator(";");
		
		parent.addChildItem(seq);
		
		// Expression
		seq.setExpr(fParsers.propertyExprParser().sequence_expression());
		
		fLexer.readKeyword("endsequence");
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readId();
		}
	}

}

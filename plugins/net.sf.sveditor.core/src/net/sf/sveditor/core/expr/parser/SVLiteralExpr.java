package net.sf.sveditor.core.expr.parser;

public class SVLiteralExpr extends SVExpr {
	
	private String					fLiteral;
	
	public SVLiteralExpr(String literal) {
		super(SVExprType.Literal);
		
		fLiteral = literal;
	}
	
	public String getValue() {
		return fLiteral;
	}

}

package net.sf.sveditor.core.expr.parser;

public class SVExprParseException extends Exception {
	
	private static final long serialVersionUID = 4403018861977065475L;

	public SVExprParseException(String msg) {
		super(msg);
	}
	
	public SVExprParseException(Exception e) {
		super(e);
	}

}

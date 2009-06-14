package net.sf.sveditor.core.constraint.parser;

public class ParseException extends Exception {
	
	private static final long serialVersionUID = 4403018861977065475L;

	public ParseException(String msg) {
		super(msg);
	}
	
	public ParseException(Exception e) {
		super(e);
	}

}

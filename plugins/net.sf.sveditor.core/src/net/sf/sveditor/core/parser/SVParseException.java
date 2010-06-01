package net.sf.sveditor.core.parser;

public class SVParseException extends Exception {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private SVParseException(String msg) {
		super(msg);
	}
	
	
	public static SVParseException createParseException(String msg) {
		return new SVParseException(msg);
	}
}

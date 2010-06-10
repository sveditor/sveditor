package net.sf.sveditor.core.parser;

public class SVParseException extends Exception {
	
	private String						fMessage;
	private String						fFilename;
	private int							fLineno;
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private SVParseException(String msg, String filename, int lineno) {
		super(filename + ":" + lineno + " " + msg);
		fMessage  = msg;
		fFilename = filename;
		fLineno = lineno;
	}
	
	public String getFilename() {
		return fFilename;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public static SVParseException createParseException(String msg, String filename, int lineno) {
		return new SVParseException(msg, filename, lineno);
	}
}

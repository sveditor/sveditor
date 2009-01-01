package net.sf.sveditor.core.parser;

public class SVLocation {
	private int						fLineno;
	private int						fLinepos;
	
	public SVLocation(int lineno, int linepos) {
		fLineno  = lineno;
		fLinepos = linepos;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public int getLinepos() {
		return fLinepos;
	}

}

package net.sf.sveditor.core.scanner;

public class ScanLocation implements IScanLocation {
	private String			fFile;
	private int				fLineno;
	private int				fLinepos;
	
	public ScanLocation(String file, int lineno, int linepos) {
		fFile = file;
		fLineno = lineno;
		fLinepos = linepos;
	}
	
	public String getFileName() {
		return fFile;
	}
	
	public int getLineNo() {
		return fLineno;
	}
	
	public int getLinePos() {
		return fLinepos;
	}
}

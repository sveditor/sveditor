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
	
	public void setFileName(String name) {
		fFile = name;
	}
	
	public int getLineNo() {
		return fLineno;
	}
	
	public void setLineNo(int num) {
		fLineno = num;
	}
	
	public int getLinePos() {
		return fLinepos;
	}
	
	public void setLinePos(int pos) {
		fLinepos = pos;
	}
}

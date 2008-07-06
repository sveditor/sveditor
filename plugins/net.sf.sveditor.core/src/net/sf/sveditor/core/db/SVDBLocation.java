package net.sf.sveditor.core.db;

public class SVDBLocation {
	private SVDBFile		fFile;
	private int				fLine;
	private int				fPos;
	
	public SVDBLocation(SVDBFile file, int line, int pos) {
		fFile = file;
		fLine = line;
		fPos  = pos;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}
	
	public int getLine() {
		return fLine;
	}
	
	public int getPos() {
		return fPos;
	}
}

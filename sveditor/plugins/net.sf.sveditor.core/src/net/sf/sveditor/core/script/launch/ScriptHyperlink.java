package net.sf.sveditor.core.script.launch;

public class ScriptHyperlink {
	private int				fOffset;
	private int				fLength;
	private String			fPath;
	private int				fLineno=-1;
	
	public ScriptHyperlink(String path, int offset, int length) {
		fPath = path;
		fOffset = offset;
		fLength = length;
	}
	
	public String getPath() {
		return fPath;
	}
	
	public int getOffset() {
		return fOffset;
	}
	
	public int getLength() {
		return fLength;
	}

	public void setLineno(int lineno) {
		fLineno = lineno;
	}
	
	public int getLineno() {
		return fLineno;
	}
}

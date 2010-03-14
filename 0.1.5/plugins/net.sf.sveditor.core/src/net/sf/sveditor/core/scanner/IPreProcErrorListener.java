package net.sf.sveditor.core.scanner;

public interface IPreProcErrorListener {
	
	void preProcError(String msg, String filename, int lineno);

}

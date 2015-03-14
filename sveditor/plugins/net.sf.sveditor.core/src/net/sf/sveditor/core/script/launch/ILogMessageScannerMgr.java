package net.sf.sveditor.core.script.launch;

public interface ILogMessageScannerMgr {
	
	void setWorkingDirectory(String path, ILogMessageScanner scanner);
	
	String getWorkingDirectory();

	void addMessage(ScriptMessage msg);
	
}

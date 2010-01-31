package net.sf.sveditor.core.log;

public interface ILogListener {
	int Type_Info  = 1;
	int Type_Debug = 2;
	int Type_Error = 3;
	
	void message(ILogHandle handle, int type, int level, String message);

}

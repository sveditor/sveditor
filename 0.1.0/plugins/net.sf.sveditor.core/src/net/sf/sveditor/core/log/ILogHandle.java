package net.sf.sveditor.core.log;

public interface ILogHandle {
	
	String getName();
	
	void init(ILogListener parent);
	
	void print(int type, int level, String msg);
	
	void println(int type, int level, String msg);
	
}

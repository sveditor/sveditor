package net.sf.sveditor.core.log;

public class LogHandle implements ILogHandle {
	private String			fName;
	private ILogListener	fListener;
	private int				fDebugLevel = 10;
	
	public LogHandle(String name) {
		fName = name;
	}
	
	public void init(ILogListener parent) {
		fListener = parent;
	}
	
	public String getName() {
		return fName;
	}

	@Override
	public void print(int type, int level, String msg) {
	}

	@Override
	public void println(int type, int level, String msg) {
		fListener.message(this, type, level, msg);
	}
	
	public void debug(String msg) {
		println(ILogListener.Type_Debug, fDebugLevel, msg);
	}
	
	public void error(String msg) {
		println(ILogListener.Type_Error, fDebugLevel, msg);
	}

}

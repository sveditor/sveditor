package net.sf.sveditor.core.log;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class LogFactory implements ILogListener {
	
	private static LogFactory			fDefault;
	private Map<String, LogHandle>		fLogHandleMap;
	private List<ILogListener> 			fLogListeners;
	
	public LogFactory() {
		fLogHandleMap = new HashMap<String, LogHandle>();
		fLogListeners = new ArrayList<ILogListener>();
	}
	
	
	public static LogFactory getDefault() {
		if (fDefault == null) {
			fDefault = new LogFactory();
		}
		return fDefault;
	}
	
	public LogHandle getLogHandle(String name) {
		if (!fLogHandleMap.containsKey(name)) {
			LogHandle handle = new LogHandle(name);
			handle.init(this);
			fLogHandleMap.put(name, handle);
		}
		return fLogHandleMap.get(name);
	}

	public void addLogListener(ILogListener l) {
		fLogListeners.add(l);
	}
	
	public void removeLogListener(ILogListener l) {
		fLogListeners.remove(l);
	}


	@Override
	public void message(ILogHandle handle, int type, int level, String message) {
		for (ILogListener l : fLogListeners) {
			l.message(handle, type, level, message);
		}
	}
	
	
	

}

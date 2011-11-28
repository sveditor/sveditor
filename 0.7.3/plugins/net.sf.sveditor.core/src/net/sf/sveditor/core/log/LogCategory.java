package net.sf.sveditor.core.log;

import java.util.ArrayList;
import java.util.List;

public class LogCategory {
	private String				fCategory;
	private int					fLogLevel;
	private List<ILogHandle>	fLogHandles;
	
	public LogCategory(String category, int level) {
		fCategory = category;
		fLogLevel = level;
		fLogHandles = new ArrayList<ILogHandle>();
	}
	
	public String getCategory() {
		return fCategory;
	}
	
	public void setLogLevel(int level) {
		for (ILogHandle h : fLogHandles) {
			h.setDebugLevel(level);
		}
	}
	
	public int getLogLevel() {
		return fLogLevel;
	}
	
	public void addLogHandle(ILogHandle handle) {
		handle.setDebugLevel(fLogLevel);
		fLogHandles.add(handle);
	}
	
	public void removeLogHandle(ILogHandle handle) {
		fLogHandles.remove(handle);
	}

}

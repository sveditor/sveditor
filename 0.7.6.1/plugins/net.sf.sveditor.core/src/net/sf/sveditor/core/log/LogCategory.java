package net.sf.sveditor.core.log;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

public class LogCategory {
	private String							fCategory;
	private int								fLogLevel;
	private List<WeakReference<ILogHandle>>	fLogHandles;
	
	public LogCategory(String category, int level) {
		fCategory = category;
		fLogLevel = level;
		fLogHandles = new ArrayList<WeakReference<ILogHandle>>();
	}
	
	public String getCategory() {
		return fCategory;
	}
	
	public void setLogLevel(int level) {
		for (int i=0; i<fLogHandles.size(); i++) {
			WeakReference<ILogHandle> lr = fLogHandles.get(i);
			if (lr.get() == null) {
				fLogHandles.remove(i);
				i--;
			} else {
				lr.get().setDebugLevel(level);
			}
		}
	}
	
	public int getLogLevel() {
		return fLogLevel;
	}
	
	public void addLogHandle(ILogHandle handle) {
		handle.setDebugLevel(fLogLevel);
		fLogHandles.add(new WeakReference<ILogHandle>(handle));
	}
	
	public void removeLogHandle(ILogHandle handle) {
		fLogHandles.remove(handle);
	}

}

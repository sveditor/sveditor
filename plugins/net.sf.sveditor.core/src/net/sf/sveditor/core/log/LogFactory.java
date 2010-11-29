/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


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
	
	public static LogHandle getLogHandle(String name) {
		LogFactory f = getDefault();
		
		if (!f.fLogHandleMap.containsKey(name)) {
			LogHandle handle = new LogHandle(name);
			handle.init(f);
			f.fLogHandleMap.put(name, handle);
		}
		return f.fLogHandleMap.get(name);
	}

	public void addLogListener(ILogListener l) {
		synchronized (fLogListeners) {
			fLogListeners.add(l);
		}
	}
	
	public void removeLogListener(ILogListener l) {
		synchronized (fLogListeners) {
			fLogListeners.remove(l);
		}
	}


	public void message(ILogHandle handle, int type, int level, String message) {
		synchronized (fLogListeners) {
			for (ILogListener l : fLogListeners) {
				l.message(handle, type, level, message);
			}
		}
	}
	
	
	

}

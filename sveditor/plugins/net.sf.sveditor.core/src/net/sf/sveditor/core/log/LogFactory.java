/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.log;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class LogFactory implements ILogListener {
	
	private static LogFactory					fDefault;
	private Map<String, LogHandle>				fLogHandleMap;
	private int									fLogLevel = 0;
	private Map<String, LogCategory>			fLogHandleCategoryMap;
	private List<WeakReference<ILogListener>>	fLogListeners;
	
	public LogFactory() {
		fLogHandleMap = new HashMap<String, LogHandle>();
		fLogHandleCategoryMap = new HashMap<String, LogCategory>();
		fLogListeners = new ArrayList<WeakReference<ILogListener>>();
	}
	
	public synchronized static LogFactory getDefault() {
		if (fDefault == null) {
			fDefault = new LogFactory();
		}
		return fDefault;
	}
	
	public static synchronized LogHandle getLogHandle(String name) {
		return getLogHandle(name, ILogHandle.LOG_CAT_DEFAULT);
	}
	
	public void setLogLevel(String category, int level) {
		if (category == null) {
			// all categories
			fLogLevel = level;
			for (Entry<String, LogCategory> e : fLogHandleCategoryMap.entrySet()) {
				e.getValue().setLogLevel(level);
			}
		} else {
			LogCategory cat;
			if (fLogHandleCategoryMap.containsKey(category)) {
				cat = new LogCategory(category, level);
				fLogHandleCategoryMap.put(category, cat);
			} else {
				cat = fLogHandleCategoryMap.get(category);
			}
			cat.setLogLevel(level);
		}
	}

	public static synchronized LogHandle getLogHandle(String name, String category) {
		LogFactory f = getDefault();
		boolean created = false;
		LogHandle handle = null;
		
		synchronized (f.fLogHandleMap) {
			if (!f.fLogHandleMap.containsKey(name)) {
				handle = new LogHandle(name, category);
				handle.init(f);
				f.fLogHandleMap.put(name, handle);
				created = true;
			} else {
				handle = f.fLogHandleMap.get(name);
			}
		}
		
		if (created) {
			synchronized (f.fLogHandleCategoryMap) {
				LogCategory cat;
				if (!f.fLogHandleCategoryMap.containsKey(handle.getCategory())) {
					cat = new LogCategory(handle.getCategory(), f.fLogLevel);
					f.fLogHandleCategoryMap.put(handle.getCategory(), cat);
				} else {
					cat = f.fLogHandleCategoryMap.get(handle.getCategory());
				}
				cat.addLogHandle(handle);
			}
		}

		return handle;
	}

	public static void removeLogHandle(LogHandle log) {
		LogFactory f = getDefault();
		synchronized (f.fLogHandleMap) {
			f.fLogHandleMap.remove(log.getName());
		}
		synchronized (f.fLogHandleCategoryMap) {
			f.fLogHandleCategoryMap.get(log.getCategory()).removeLogHandle(log);
		}
	}

	public void addLogListener(ILogListener l) {
		synchronized (fLogListeners) {
			fLogListeners.add(new WeakReference<ILogListener>(l));
		}
	}
	
	public void removeLogListener(ILogListener l) {
		synchronized (fLogListeners) {
			for (int i=0; i<fLogListeners.size(); i++) {
				if (fLogListeners.get(i).get() == l) {
					fLogListeners.remove(i);
				}
			}
		}
	}

	public static void note(String msg) {
		getDefault().message(null, ILogListener.Type_Info, 0, msg);
	}

	public void message(ILogHandle handle, int type, int level, String message) {
		synchronized (fLogListeners) {
			for (int i=0; i<fLogListeners.size(); i++) {
				WeakReference<ILogListener> lr = fLogListeners.get(i);

				if (lr.get() == null) {
					fLogListeners.remove(i);
					i--;
				} else {
					lr.get().message(handle, type, level, message);
				}
			}
		}
	}

}

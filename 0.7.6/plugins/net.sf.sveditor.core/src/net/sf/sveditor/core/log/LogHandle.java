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

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

public class LogHandle implements ILogHandle {
	private String						fName;
	private String						fCategory;
	private ILogListener				fListener;
	private int							fDebugLevel = 10;
	private int							fIndent;
	private List<WeakReference<ILogLevelListener>>		fLogLevelListeners;
	
	public LogHandle(String name) {
		this(name, LOG_CAT_DEFAULT);
	}

	public LogHandle(String name, String category) {
		fName = name;
		fCategory = category;
		fLogLevelListeners = new ArrayList<WeakReference<ILogLevelListener>>();
	}

	public void init(ILogListener parent) {
		fListener = parent;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getCategory() {
		return fCategory;
	}
	
	public void addLogLevelListener(ILogLevelListener l) {
		fLogLevelListeners.add(new WeakReference<ILogLevelListener>(l));
	}
	
	public void setDebugLevel(int level) {
		if (fDebugLevel != level) {
			fDebugLevel = level;
			// notify listeners
			for (int i=0; i<fLogLevelListeners.size(); i++) {
				WeakReference<ILogLevelListener> l = fLogLevelListeners.get(i);
				if (l.get() == null) {
					fLogLevelListeners.remove(i);
					i--;
				} else {
					l.get().logLevelChanged(this);
				}
			}
		}
		fDebugLevel = level;
	}
	
	public int getDebugLevel() {
		return fDebugLevel;
	}

	public boolean isEnabled() {
		return (fDebugLevel > 0);
	}

	public void print(int type, int level, String msg) {
	}

	public void println(int type, int level, String msg) {
		fListener.message(this, type, level, msg);
	}
	
	public void note(String msg) {
		println(ILogListener.Type_Info, 0, msg);
	}
	
	public void debug(String msg) {
		println(ILogListener.Type_Debug, fDebugLevel, 
				(fIndent > 0)?(indent(fIndent) + msg):msg);
	}

	public void debug(String msg, Exception e) {
		int level = ILogListener.Type_Error+ILogListener.Type_Debug;
		println(level, fDebugLevel, msg);
		println(level, fDebugLevel, e.getMessage());
		for (StackTraceElement s_e : e.getStackTrace()) {
			String m = "    at " + 
					s_e.getClassName() + "." + s_e.getMethodName() + "(" +
					s_e.getFileName() + ":" + s_e.getLineNumber() + ")";
			println(level, fDebugLevel, m);
		}
	}

	public void enter(String msg) {
		debug(msg);
		fIndent++;
	}

	public void leave(String msg) {
		if (fIndent > 0) {
			fIndent--;
		}
		debug(msg);
	}

	public void error(String msg) {
		println(ILogListener.Type_Error, fDebugLevel, msg);
	}

	public void error(String msg, Exception e) {
		println(ILogListener.Type_Error, fDebugLevel, msg);
		println(ILogListener.Type_Error, fDebugLevel, e.getMessage());
		for (StackTraceElement s_e : e.getStackTrace()) {
			println(ILogListener.Type_Error, fDebugLevel, "    at " + 
					s_e.getClassName() + "." + s_e.getMethodName() + "(" +
					s_e.getFileName() + ":" + s_e.getLineNumber() + ")");
		}
	}
	
	private String indent(int ind) {
		String ret = "";
		while (ind-- > 0) {
			ret += "    ";
		}
		
		return ret;
	}

}

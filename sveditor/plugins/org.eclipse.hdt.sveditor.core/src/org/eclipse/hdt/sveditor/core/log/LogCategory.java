/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.log;

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
		fLogLevel = level;
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

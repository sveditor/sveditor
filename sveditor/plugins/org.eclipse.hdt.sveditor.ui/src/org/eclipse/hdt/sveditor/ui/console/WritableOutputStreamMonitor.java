/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.ui.console;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.model.IFlushableStreamMonitor;
import org.eclipse.debug.core.model.IStreamMonitor;

public class WritableOutputStreamMonitor implements IFlushableStreamMonitor, IStreamMonitor {
	private List<IStreamListener>		fListeners;
	private boolean						fIsBuffered;
	
	public WritableOutputStreamMonitor() {
		fListeners = new ArrayList<IStreamListener>();
	}

	@Override
	public void addListener(IStreamListener listener) {
		synchronized (fListeners) {
			fListeners.add(listener);
		}
	}

	@Override
	public String getContents() {
		System.out.println("Error: getContents");
		return "";
	}

	@Override
	public void removeListener(IStreamListener listener) {
		synchronized (fListeners) {
			fListeners.remove(listener);
		}
	}

	@Override
	public void flushContents() {
		System.out.println("TODO: flush");
	}
	
	public void write(String input) {
		synchronized (fListeners) {
			for (IStreamListener l : fListeners) {
				l.streamAppended(input, this);
			}
		}
	}

	@Override
	public void setBuffered(boolean buffer) {
		fIsBuffered = buffer;
	}

	@Override
	public boolean isBuffered() {
		return fIsBuffered;
	}

}

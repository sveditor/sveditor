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
package net.sf.sveditor.core.tests;

import java.util.Map;

import org.eclipse.hdt.sveditor.core.ISVProjectBuilderListener;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class ProjectBuildMonitor implements ISVProjectBuilderListener {
	private Object					fSemaphore = new Object();
	private int						fKind = -1;
	private LogHandle				fLog = LogFactory.getLogHandle("ProjectBuildMonitor");
	

	@Override
	public void build_start(int kind, Map<String, String> args) {
		fLog.debug("build_start: " + kind);
	}

	@Override
	public void build_complete(int kind, Map<String, String> args) {
		fLog.debug("build_complete: " + kind);
		// TODO Auto-generated method stub
		fKind = kind;
		synchronized (fSemaphore) {
			fSemaphore.notifyAll();
		}
	}
	
	public void reset() {
		fKind = -1;
	}
	
	public boolean wait(int kind, int ms) {
		fLog.debug("--> wait: " + kind);
		
		if (fKind == kind) {
			fLog.debug("<-- wait: " + kind + " early escape");
			return true;
		}
		
		try {
			synchronized (fSemaphore) {
				fSemaphore.wait(ms);
			}
		} catch (InterruptedException e) {}
	
		fLog.debug("<-- wait: " + kind + " " + fKind);
		return (fKind == kind);
	}

}

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


package org.eclipse.hdt.sveditor.core.job_mgr;

import org.eclipse.core.runtime.IProgressMonitor;

public interface IJob {
	
	void init(String name, Runnable runnable);
	
	String getName();
	
	void setPriority(int p);
	
	int getPriority();
	
	void run(IProgressMonitor monitor);
	
	void addListener(IJobListener l);
	
	void removeListener(IJobListener l);
	
	void clearListeners();
	
	void join();
	
	boolean join(int wait_ms);
	
}

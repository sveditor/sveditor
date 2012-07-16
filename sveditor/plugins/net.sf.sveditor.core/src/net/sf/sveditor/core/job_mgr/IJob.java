/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.job_mgr;

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

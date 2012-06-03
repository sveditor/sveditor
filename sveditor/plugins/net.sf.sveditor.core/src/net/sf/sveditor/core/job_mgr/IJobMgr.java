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

public interface IJobMgr {
	
	IJob createJob();
	
	void queueJob(IJob job);
	
	void addJobListener(IJobListener l);
	
	void removeJobListener(IJobListener l);
	
	void dispose();

}

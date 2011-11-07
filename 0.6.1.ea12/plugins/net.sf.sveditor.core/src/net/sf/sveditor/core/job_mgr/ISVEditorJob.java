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

public interface ISVEditorJob {
	
	String getName();
	
	/**
	 * Returns the 'kind' of job. This controls which queue the job is placed in
	 * 
	 * @return
	 */
	String getKind();
	
	void pre_run();
	
	void run(IProgressMonitor monitor) throws SVJobException;
	
	void post_run();
	
	void addListener(ISVEditorJobListener l);
	
	void removeListener(ISVEditorJobListener l);
	
}

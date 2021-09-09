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
package org.sveditor.core.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.project.SVDBProjectManager;
import org.sveditor.core.log.ILogLevel;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

public class SVProjectBuilder extends IncrementalProjectBuilder implements ILogLevel {
	private LogHandle							fLog;
	
	public static final String BUILDER_ID = "org.sveditor.core.SVProjectBuilder";

	public SVProjectBuilder() {
		// TODO Auto-generated constructor stub
		fLog = LogFactory.getLogHandle("SVProjectBuilder");
	}
	
	@Override
	protected IProject[] build(
			int 					kind, 
			Map<String, String> 	args,
			IProgressMonitor 		monitor) throws CoreException {
		IProject 			p = getProject();
		SVDBProjectManager 	pmgr = SVCorePlugin.getDefault().getProjMgr();

		// Special test mode enabled
		if (SVCorePlugin.isTestModeBuilderDisabled()) {
			return null;
		}
		
		SVBuilderProcess process = new SVBuilderProcess(monitor, p);
	
		pmgr.startBuild(process, p, kind, args);
		
		process.build(kind, args, getDelta(p));

		pmgr.endBuild(p, kind, args);
		
		// Don't need any delta right now...
		return null;
	}

}

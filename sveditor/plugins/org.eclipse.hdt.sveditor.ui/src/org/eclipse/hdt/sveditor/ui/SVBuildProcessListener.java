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
package org.eclipse.hdt.sveditor.ui;

import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.Launch;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.hdt.sveditor.core.builder.ISVBuildProcessListener;
import org.eclipse.hdt.sveditor.core.builder.SVBuilderProcess;

import org.eclipse.hdt.sveditor.ui.console.SVConsoleManager;
import org.eclipse.hdt.sveditor.ui.console.SVGlobalConsole;
import org.eclipse.hdt.sveditor.ui.console.SVProcessConsole;

public class SVBuildProcessListener implements ISVBuildProcessListener {
	private SVGlobalConsole			fGlobalBuildConsole;
	
	private IStreamListener fStdoutListener = new IStreamListener() {
		
		@Override
		public void streamAppended(String text, IStreamMonitor monitor) {
			fGlobalBuildConsole.stdout(text);
		}
	};
	
	private IStreamListener fStderrListener = new IStreamListener() {
		
		@Override
		public void streamAppended(String text, IStreamMonitor monitor) {
			fGlobalBuildConsole.stderr(text);
		}
	};

	@Override
	public void buildProcess(Process p) {
//		if (fGlobalBuildConsole == null) {
//			fGlobalBuildConsole = SVConsoleManager.getDefault().openConsole(
//					"SV Global Build Console", 
//					"sve.build");
//		}
		
    	ILaunch launch = new Launch(null, "run", null); 
    	IProject project = ((SVBuilderProcess)p).getProject();
    	IProcess process = DebugPlugin.newProcess(launch, p, 
    			"SV Build Console [" + project.getName() + "]");
    	process.setAttribute(IProcess.ATTR_PROCESS_TYPE, "sve.build");
		SVProcessConsole console = SVConsoleManager.getDefault().openProcessConsole(
				process, null);
		
//		// add stream listeners to direct project build to the global console
//		console.getStreamsProxy().getOutputStreamMonitor().addListener(fStdoutListener);
//		console.getStreamsProxy().getErrorStreamMonitor().addListener(fStderrListener);
		
	}

}

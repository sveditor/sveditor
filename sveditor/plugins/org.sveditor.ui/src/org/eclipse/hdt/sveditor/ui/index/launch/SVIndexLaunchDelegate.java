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
package org.eclipse.hdt.sveditor.ui.index.launch;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.swt.widgets.Display;

public class SVIndexLaunchDelegate implements ILaunchConfigurationDelegate {

	@Override
	public void launch(
			ILaunchConfiguration 	configuration, 
			String 					mode, 
			ILaunch 				launch, 
			IProgressMonitor 		monitor) throws CoreException {
	
		Process p = (Process)configuration.getAttributes().get("PROCESS");
		
		Map<String, String> attr = new HashMap<String, String>();
		System.out.println("buildProcess");
		attr.put(IProcess.ATTR_PROCESS_TYPE, "sve.build");

		DebugPlugin.newProcess(launch, p, "Foo", attr);
	
		// Execute any events
		while (Display.getDefault().readAndDispatch()) { }
	}
}

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
package org.sveditor.ui.console;

import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.ui.console.IConsoleColorProvider;
import org.eclipse.jface.resource.ImageDescriptor;

public class SVProcessConsole extends SVConsole {
    private IProcess					fProcess;
	
	public SVProcessConsole(
			SVConsoleManager	mgr,
			IProcess			process,
			ImageDescriptor		img) {
		super(mgr, 
				process.getLabel(), 
				process.getAttribute(IProcess.ATTR_PROCESS_TYPE), 
				img);

		fProcess    = process;
		fStreamsProxy = fProcess.getStreamsProxy();
		fColorProvider = fConsoleMgr.getColorProvider(
				process.getAttribute(IProcess.ATTR_PROCESS_TYPE));
		fColorProvider.connect(process, this);
	}

	@Override
	public IProcess getProcess() {
		return fProcess;
	}

	
}

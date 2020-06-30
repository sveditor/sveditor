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
package org.eclipse.hdt.sveditor.ui.console;

import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.internal.ui.preferences.IDebugPreferenceConstants;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.console.IConsole;
import org.eclipse.debug.ui.console.IConsoleColorProvider;
import org.eclipse.swt.graphics.Color;

public class SVBuildConsoleColorProvider implements IConsoleColorProvider {

	@Override
	public boolean isReadOnly() {
		return true;
	}

	@Override
	public Color getColor(String streamIdentifer) {
		Color ret = null;
		if (IDebugUIConstants.ID_STANDARD_OUTPUT_STREAM.equals(streamIdentifer)) {
			ret = DebugUIPlugin.getPreferenceColor(IDebugPreferenceConstants.CONSOLE_SYS_OUT_COLOR);
		}
		if (IDebugUIConstants.ID_STANDARD_ERROR_STREAM.equals(streamIdentifer)) {
			ret = DebugUIPlugin.getPreferenceColor(IDebugPreferenceConstants.CONSOLE_SYS_ERR_COLOR);
		}		
		if (IDebugUIConstants.ID_STANDARD_INPUT_STREAM.equals(streamIdentifer)) {
			ret = DebugUIPlugin.getPreferenceColor(IDebugPreferenceConstants.CONSOLE_SYS_IN_COLOR);
		}			
		
		return ret;
	}

	@Override
	public void connect(IProcess process, IConsole console) {
		IStreamsProxy streamsProxy = process.getStreamsProxy();
		if (streamsProxy != null) {
			console.connect(streamsProxy);
		}
	}

	@Override
	public void disconnect() {
		// TODO Auto-generated method stub

	}

}

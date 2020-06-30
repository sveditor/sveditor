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

import java.io.IOException;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.debug.internal.core.OutputStreamMonitor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.console.IOConsoleInputStream;
import org.eclipse.ui.console.IOConsoleOutputStream;

public class SVGlobalConsole extends SVConsole implements IStreamsProxy {
	private WritableOutputStreamMonitor	fErrorMonitor;
	private WritableOutputStreamMonitor	fOutputMonitor;
	
	public SVGlobalConsole(
			SVConsoleManager	mgr,
			String				name,
			String				type,
			ImageDescriptor		img) {
		super(mgr, name, type, img);
		
		fErrorMonitor = new WritableOutputStreamMonitor();
		fOutputMonitor = new WritableOutputStreamMonitor();
		
		fColorProvider = fConsoleMgr.getColorProvider(type);
		fColorProvider.connect(fDummyProcess, this);
	}
	
	@Override
	public IStreamMonitor getErrorStreamMonitor() {
		return fErrorMonitor;
	}

	@Override
	public IStreamMonitor getOutputStreamMonitor() {
		return fOutputMonitor;
	}
	
	public void stdout(String line) {
		fOutputMonitor.write(line);
	}
	
	public void stderr(String line) {
		fErrorMonitor.write(line);
	}

	@Override
	public void write(String input) throws IOException {
		fOutputMonitor.write(input);
	}

	private IProcess fDummyProcess = new IProcess() {
		
		@Override
		public void terminate() throws DebugException { }
		
		@Override
		public boolean isTerminated() {
			return false;
		}
		
		@Override
		public boolean canTerminate() {
			return false;
		}
		
		@Override
		public <T> T getAdapter(Class<T> adapter) {
			// TODO Auto-generated method stub
			return null;
		}
		
		@Override
		public void setAttribute(String key, String value) { }
		
		@Override
		public IStreamsProxy getStreamsProxy() {
			return SVGlobalConsole.this;
		}
		
		@Override
		public ILaunch getLaunch() {
			return null;
		}
		
		@Override
		public String getLabel() {
			return getName();
		}
		
		@Override
		public int getExitValue() throws DebugException {
			return 0;
		}
		
		@Override
		public String getAttribute(String key) {
			// TODO Auto-generated method stub
			return null;
		}
	};
}

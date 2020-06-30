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
package org.eclipse.hdt.sveditor.ui.script.launch;


import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.console.IConsole;
import org.eclipse.debug.ui.console.IConsoleLineTracker;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.script.launch.BuildScriptLauncherConstants;
import org.eclipse.hdt.sveditor.core.script.launch.ILogMessageListener;
import org.eclipse.hdt.sveditor.core.script.launch.ILogMessageScanner;
import org.eclipse.hdt.sveditor.core.script.launch.LogMessageScannerMgr;
import org.eclipse.hdt.sveditor.core.script.launch.SVScriptProblem;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessageScannerDescriptor;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessageScannerRegistry;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage.MessageType;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IRegion;

public class ScriptLineTracker implements IConsoleLineTracker {
	
	private LogMessageScannerMgr				fScannerMgr;
	private IConsole							fConsole;

	@Override
	public void init(IConsole console) {
		fConsole = console;
		
		ILaunch l = console.getProcess().getLaunch();
		ILaunchConfiguration configuration  = l.getLaunchConfiguration();

		String scanners = null;
		String wd = null;
		
		try {
			wd = configuration.getAttribute(BuildScriptLauncherConstants.WORKING_DIR, System.getProperty("user.dir"));
			scanners = configuration.getAttribute(BuildScriptLauncherConstants.SCANNERS, "");
		} catch (CoreException e) {
			e.printStackTrace();
			return;
		}
		
		ScriptMessageScannerRegistry rgy = new ScriptMessageScannerRegistry();
		fScannerMgr = new LogMessageScannerMgr(wd);
		fScannerMgr.addMessageListener(msgScannerListener);
		
		ScriptConsolePatternMatcherFactory.addPatternMatchers(fScannerMgr, fConsole);
	
		if (scanners != null && scanners.length() > 0) {
			for (String id : scanners.split(",")) {
				id = id.trim();

				if (id.equals("")) {
					continue;
				}

				ScriptMessageScannerDescriptor d = rgy.getDescriptor(id);

				if (d != null) {
					ILogMessageScanner scanner = d.getScanner();

					if (scanner != null) {
						fScannerMgr.addScanner(scanner);
					}
				}
			}
		} else {
			// Add all scanners
			for (ScriptMessageScannerDescriptor d : rgy.getDescriptors()) {
				fScannerMgr.addScanner(d.getScanner());
			}
		}
		
	}

	@Override
	public void lineAppended(IRegion line) {
		try {
			String msg = fConsole.getDocument().get(line.getOffset(), line.getLength());
			fScannerMgr.line(msg);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void dispose() {
		fScannerMgr.close();
	}

	private ILogMessageListener msgScannerListener = new ILogMessageListener() {
		
		@Override
		public void message(ScriptMessage msg) {
			String path = msg.getPath();
			IFile file[] = SVFileUtils.findWorkspaceFiles(path);

			// Skip infos for now
			if (msg.getType() != MessageType.Note) {
				if (file != null && file.length > 0) {
					for (IFile f : file) {
						try {
							String mt = msg.getMarkerType();
							
							if (mt == null) {
								mt = SVScriptProblem.ID;
							}
							
							IMarker m = f.createMarker(mt);
							
							switch (msg.getType()) {
								case Error:
									m.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
									break;
								case Warning:
									m.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
									break;
								case Note:
									m.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
									break;
							}
							m.setAttribute(IMarker.LINE_NUMBER, msg.getLineno());
							m.setAttribute(IMarker.MESSAGE, msg.getMessage());
						} catch (CoreException e) {
							//
						}
					}
				}
			}
		}

	};
}

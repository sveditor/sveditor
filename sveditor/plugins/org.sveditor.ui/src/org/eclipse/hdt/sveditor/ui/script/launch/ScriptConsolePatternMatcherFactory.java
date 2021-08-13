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

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.ui.console.IConsole;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.script.launch.ILogMessageScanner;
import org.eclipse.hdt.sveditor.core.script.launch.ILogMessageScannerMgr;
import org.eclipse.ui.console.IPatternMatchListener;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;
import org.eclipse.hdt.sveditor.ui.console.SVEMessageConsole;

public class ScriptConsolePatternMatcherFactory {
	
	public static void addPatternMatchers(ILogMessageScannerMgr mgr, IConsole console) {
		LogHandle log = LogFactory.getLogHandle("ScriptConsolePatternMatcherFactory");
		IExtensionPoint ep = Platform.getExtensionRegistry().getExtensionPoint(
				SVUiPlugin.PLUGIN_ID, "svScriptPatternMatchers");
		
		for (IExtension ext : ep.getExtensions()) {
			for (IConfigurationElement ce : ext.getConfigurationElements()) {
				Object obj = null;
				try {
					obj = ce.createExecutableExtension("class");
				} catch (CoreException e) {
					log.error("Failed to create class for extension " + ce.getAttribute("name"), e);
					continue;
				}
			
				if (!(obj instanceof IPatternMatchListener)) {
					log.error("Class for " + ce.getAttribute("name") + " does not extend IPatternMatchListener");
					continue;
				}
				
				if (obj instanceof ILogMessageScanner) {
					((ILogMessageScanner)obj).init(mgr);
				}
				
				IPatternMatchListener l = (IPatternMatchListener)obj;
				console.addPatternMatchListener(l);
			}
		}
	}

}

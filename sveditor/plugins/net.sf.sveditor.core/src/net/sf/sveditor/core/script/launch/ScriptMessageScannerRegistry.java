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
package net.sf.sveditor.core.script.launch;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.script.launch.ScriptMessageScannerDescriptor.ScannerType;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;

public class ScriptMessageScannerRegistry {
	private List<ScriptMessageScannerDescriptor>		fDescriptors;
	
	public ScriptMessageScannerRegistry() {
		fDescriptors = new ArrayList<ScriptMessageScannerDescriptor>();
		update();
	}
	
	public List<ScriptMessageScannerDescriptor> getDescriptors() {
		return fDescriptors;
	}
	
	public ScriptMessageScannerDescriptor getDescriptor(String id) {
		for (ScriptMessageScannerDescriptor d : fDescriptors) {
			if (d.getId().equals(id)) {
				return d;
			}
		}
		return null;
	}

	public void update() {
		IExtensionRegistry rgy = Platform.getExtensionRegistry();
		
		fDescriptors.clear();
		
		IExtensionPoint ep = rgy.getExtensionPoint(
				SVCorePlugin.PLUGIN_ID, "SVLogMessageScanners");
		
		for (IExtension log_scanners : ep.getExtensions()) {
			for (IConfigurationElement log_scanner : log_scanners.getConfigurationElements()) {
				if (!log_scanner.getName().equals("LogMessageScanner")) {
					continue;
				}
				String id = log_scanner.getAttribute("id");
				String name = log_scanner.getAttribute("name");
				ScannerType type = ScannerType.General;
				String type_s = log_scanner.getAttribute("type");
				
				if (type_s != null) {
					if (type_s.equals("build")) {
						type = ScannerType.Build;
					} else if (type_s.equals("run")) {
						type = ScannerType.Run;
					} else if (type_s.equals("general")) {
						type = ScannerType.General;
					}
				}

				ILogMessageScanner scanner = null;
				try {
					scanner = (ILogMessageScanner)log_scanner.createExecutableExtension("class");
				} catch (Exception e) {
					e.printStackTrace();
				}
				
				if (scanner != null) {
					ScriptMessageScannerDescriptor d = new ScriptMessageScannerDescriptor(
							id, name, type, scanner);
				
					fDescriptors.add(d);
				}
			}
		}
	}

}

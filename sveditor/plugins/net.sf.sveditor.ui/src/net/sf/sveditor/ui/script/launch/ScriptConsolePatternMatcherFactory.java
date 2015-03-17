package net.sf.sveditor.ui.script.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;
import org.eclipse.ui.console.IPatternMatchListener;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.script.launch.ILogMessageScanner;
import net.sf.sveditor.core.script.launch.ILogMessageScannerMgr;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.console.SVEConsole;

public class ScriptConsolePatternMatcherFactory {
	
	public static void addPatternMatchers(ILogMessageScannerMgr mgr, SVEConsole console) {
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

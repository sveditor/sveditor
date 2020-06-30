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
package net.sf.sveditor.ui.script.launch;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileLexer;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;
import org.eclipse.hdt.sveditor.core.script.launch.BuildScriptLauncherConstants;
import org.eclipse.hdt.sveditor.core.script.launch.SVScriptProblem;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptRunner;

public class ScriptLaunchDelegate implements ILaunchConfigurationDelegate {

	public ScriptLaunchDelegate() {
	}

	@Override
	public void launch(
			ILaunchConfiguration 	configuration, 
			String 					mode,
			ILaunch 				launch, 
			IProgressMonitor 		monitor) throws CoreException {
		SubMonitor subMonitor = SubMonitor.convert(monitor);

		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		String script = configuration.getAttribute(BuildScriptLauncherConstants.SCRIPT_LIST, "");
		String wd = configuration.getAttribute(BuildScriptLauncherConstants.WORKING_DIR, System.getProperty("user.dir"));
		String args_str = configuration.getAttribute(BuildScriptLauncherConstants.ARGUMENTS, "");
		
		// Expand any variables
		script = SVFileUtils.expandVars(script, null, false);
		wd = SVFileUtils.expandVars(wd, null, false);
		args_str = SVFileUtils.expandVars(args_str, null, false);

		
		String save_output_file = configuration.getAttribute("org.eclipse.debug.ui.ATTR_CAPTURE_IN_FILE", (String)null);
		
		subMonitor.beginTask("Running " + script, 1000);
		
		if (save_output_file != null) {
			try {
				IStringVariableManager vman = VariablesPlugin.getDefault().getStringVariableManager();
				save_output_file = vman.performStringSubstitution(save_output_file);
			} catch (CoreException e) { 
				save_output_file = null;
			}
			
			if (save_output_file != null) {
				
			}
		}
		
		// First, clear existing problem markers
		root.deleteMarkers(SVScriptProblem.ID, true, IResource.DEPTH_INFINITE);
	
		File wd_f = SVFileUtils.getFile(wd);
		
		if (script.startsWith("${workspace_loc}")) {
			script = SVFileUtils.getWorkspaceResource(script).getLocation().toOSString();
		}
		List<String> argv = parse_arguments(args_str);
		
		argv.add(0, script);
	
		for (int i=0; i<argv.size(); i++) {
			String arg = argv.get(i);
			
			if (arg.startsWith("${workspace_loc}")) {
				arg = SVFileUtils.getWorkspaceResource(arg).getLocation().toOSString();
			}
			
			argv.set(i, arg);
		}
		
		Process p = DebugPlugin.exec(argv.toArray(new String[argv.size()]), wd_f);
		Map<String, String> attr = new HashMap<String, String>();
		attr.put(IProcess.ATTR_PROCESS_TYPE, "sve.script");
		
		/*IProcess ip = */DebugPlugin.newProcess(launch, p, script, attr);
		
		// Finally, refresh if needed
		// TODO: This should probably be optional
//		IContainer f = SVFileUtils.findWorkspaceFolder(wd_f.getAbsolutePath());
//		if (f != null && f.exists()) {
//			f.refreshLocal(IResource.DEPTH_INFINITE, subMonitor.newChild(1));
//		}
		
		subMonitor.done();
	}
	
	private List<String> parse_arguments(String args) {
		List<String> ret = new ArrayList<String>();
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, new StringTextScanner(args));
	
		while (lexer.peek() != null) {
			String tok = lexer.eatToken();
		
			// Convert workspace path to filesystem path
			if (tok.startsWith("${workspace_loc}")) {
				IResource r = SVFileUtils.getWorkspaceResource(tok);
				tok = r.getLocation().toOSString();
			}
			ret.add(tok);
		}
		
		return ret;
	}
	
}

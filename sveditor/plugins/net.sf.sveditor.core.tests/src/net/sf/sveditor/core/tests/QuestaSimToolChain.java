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
package net.sf.sveditor.core.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.LogHandle;

public class QuestaSimToolChain implements ISimToolchain {
	private boolean				fValid;
	private String				fQuestaHome;
	private String				fQuestaBindir;
	
	public QuestaSimToolChain() {
		fValid = true;
	
		fQuestaHome = System.getenv("QUESTA_HOME");
		
		if (fQuestaHome == null || !(new File(fQuestaHome).isDirectory())) {
			fValid = false;
		} else {
			// TODO: further tests?
		}
		
		fQuestaBindir = fQuestaHome + "/bin";
	}
	
	public boolean is_valid() {
		return fValid;
	}

	public void run(
			LogHandle		log,
			File 			output_dir, 
			SimBuildSpec 	build_spec,
			SimRunSpec 		run_spec) {
		
		// Create the work library
		ProcessUtils.exec(output_dir, 
				new File(output_dir, "vlib"),
				fQuestaBindir + "/vlib", "work");

		// Compile the files
		List<String> arguments = new ArrayList<String>();

		arguments.add(fQuestaBindir + "/vlog");
		for (String incdir : build_spec.getIncDirList()) {
			arguments.add("+incdir+" + incdir);
		}
		
		for (String file : build_spec.getFileList()) {
			arguments.add(file);
		}
	
		if (build_spec.getCCFlags().size() > 0) {
			StringBuilder sb = new StringBuilder();
			for (String flag : build_spec.getCCFlags()) {
				sb.append(flag + " ");
			}
			arguments.add("-ccflags");
			arguments.add(sb.toString());
		}
		
		for (String file : build_spec.getCCFiles()) {
			arguments.add(file);
		}
		
		if (log != null) {
			StringBuilder sb = new StringBuilder();
			for (String arg : arguments) {
				sb.append(arg + " ");
			}
			log.debug("Invoking: " + sb.toString());
		}
		
		ProcessUtils.exec(output_dir,
				new File(output_dir, "vlog"),
				arguments);

		arguments.clear();
		arguments.add(fQuestaBindir + "/vsim");
		arguments.add("-c");
		arguments.add("-do");
		arguments.add("run 1ms; quit -f");
		
		for (String opt : run_spec.getSimOptions()) {
			arguments.add(opt);
		}
		
		for (String top : run_spec.getTopModules()) {
			arguments.add(top);
		}
		
		if (run_spec.getTranscriptPath() != null) {
			arguments.add("-l");
			arguments.add(run_spec.getTranscriptPath());
		}
		
		ProcessUtils.exec(output_dir, 
				new File(output_dir, "vsim"), 
				arguments);
	}
}


package net.sf.sveditor.core.tests;

import java.io.File;

import net.sf.sveditor.core.log.LogHandle;

public interface ISimToolchain {
	
	boolean is_valid();
	
	void run(
			LogHandle		log,
			File			output_dir,
			SimBuildSpec	build_spec,
			SimRunSpec		run_spec);

}

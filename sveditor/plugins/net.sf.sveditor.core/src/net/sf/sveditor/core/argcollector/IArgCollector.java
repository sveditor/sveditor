package net.sf.sveditor.core.argcollector;

import java.io.File;
import java.io.IOException;
import java.util.List;

import net.sf.sveditor.core.ILineListener;

public interface IArgCollector {
	
	void addStdoutListener(ILineListener l);
	
	void addStderrListener(ILineListener l);
	
	/**
	 * Executes the compilation command. Returns the 
	 * exit code of the processing command
	 * 
	 * @return 
	 */
	int process(
			File				cwd,
			List<String>		args) throws IOException;

	/**
	 * Returns the document extracted by running the
	 * compilation command
	 * 
	 * @return
	 */
	String getArguments();
}

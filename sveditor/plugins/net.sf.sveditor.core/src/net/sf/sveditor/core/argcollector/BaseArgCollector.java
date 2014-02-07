package net.sf.sveditor.core.argcollector;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.EnvUtils;
import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.InputStreamLineReader;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;

public class BaseArgCollector implements IArgCollector {

	private File					fTmpDir;
	private File					fOutFile;
	private Process					fProcess;
	private String					fArguments;
	
	private List<ILineListener>		fStdoutListener;
	private List<ILineListener>		fStderrListener;
	
	private InputStreamLineReader	fStdoutReader;
	private InputStreamLineReader	fStderrReader;
	
	public BaseArgCollector() {
		fStdoutListener = new ArrayList<ILineListener>();
		fStderrListener = new ArrayList<ILineListener>();
	}
	
	public void addStdoutListener(ILineListener l) {
		fStdoutListener.add(l);
	}

	public void addStderrListener(ILineListener l) {
		fStderrListener.add(l);
	}
	public int process(File cwd, List<String> args) throws IOException {
		return process(cwd, args, false);
	}
	
	public int process(File cwd, List<String> args, boolean exec) throws IOException {
		// Create a temp directory
		fTmpDir = SVCorePlugin.getDefault().createWSTmpDir();
		
		File sve_collect_compiler_dir = CompilerWrapperCopier.copy(fTmpDir, true);
		
		List<String> full_args = new ArrayList<String>();
		
		full_args.addAll(args);
		
		fOutFile = new File(fTmpDir, "collected_args.f");
		
		EnvUtils env = new EnvUtils();
		env.setenv("SVE_COMPILER_ARGS_FILE", fOutFile.getAbsolutePath());
		env.prepend("PATH", sve_collect_compiler_dir.getAbsolutePath());
		env.setenv("SVE_COMPILER_ARGS_EXEC", (exec)?"1":"0");
	
		try {
			fProcess = Runtime.getRuntime().exec(
					full_args.toArray(new String[full_args.size()]),
					env.env(),
					cwd);
		} catch (IOException e) {
			SVFileUtils.delete(fTmpDir);
			fTmpDir = null;
			e.printStackTrace();
			throw e;
		}
		
		fStdoutReader = new InputStreamLineReader(
				fProcess.getInputStream(), fStdoutListener);
		fStderrReader = new InputStreamLineReader(
				fProcess.getErrorStream(), fStderrListener);
		
		fStdoutReader.start();
		fStderrReader.start();
		
		try {
			fProcess.waitFor();
			while (fStderrReader.isAlive() || fStdoutReader.isAlive()) {
				if (fStderrReader.isAlive()) {
					fStderrReader.join();
				}
				if (fStdoutReader.isAlive()) {
					fStdoutReader.join();
				}
			}
		} catch (InterruptedException e) {}

		if (fOutFile.isFile()) {
			try {
				InputStream in = new FileInputStream(fOutFile);
				fArguments = SVFileUtils.readInput(in);
				in.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		} else {
			fArguments = "";
		}

		if (fTmpDir != null) {
			SVFileUtils.delete(fTmpDir);
			fTmpDir = null;
		}
		
		return fProcess.exitValue();
	}

	public String getArguments() {
		return fArguments;
	}	

}

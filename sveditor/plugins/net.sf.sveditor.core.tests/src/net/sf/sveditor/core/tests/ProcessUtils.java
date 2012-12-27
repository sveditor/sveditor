package net.sf.sveditor.core.tests;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;

public class ProcessUtils {

	private static class IOThread extends Thread {
		private File				fOutputPath;
		private InputStream			fIn;
		
		public IOThread(File output_path, InputStream in) {
			fOutputPath = output_path;
			fIn = in;
		}

		@Override
		public void run() {
			FileOutputStream fos = null;
			
			if (fOutputPath != null) {
				try {
					fos = new FileOutputStream(fOutputPath);
				} catch (IOException e) {}
			}
			
			try {
				int ch;
				while ((ch = fIn.read()) != -1) {
					if (fos != null) {
						fos.write((char)ch);
					}
				}
			} catch (IOException e) {}
	
			try {
				if (fos != null) {
					fos.close();
				}
				fIn.close();
			} catch (IOException e) {}
		}
	}
	
	public static void exec(
			File				working_dir,
			File				output_file,
			String ...			arguments) {
		List<String> arglist = new ArrayList<String>();
		for (String arg : arguments) {
			arglist.add(arg);
		}
		
		exec(working_dir, output_file, arglist);
	}
			
	public static void exec(
			File				working_dir,
			File				output_file,
			List<String>		arguments) {
		Process p = null;
		Thread io_threads[] = new Thread[2];
		
		StringBuilder sb = new StringBuilder();
		for (String arg : arguments) {
			sb.append(arg + " ");
		}
	
		try {
			p = Runtime.getRuntime().exec(
					arguments.toArray(new String[arguments.size()]),
					null,
					working_dir);
		} catch (IOException e) {
			TestCase.fail("Failed to invoke command \"" + 
					sb.toString() + "\": " + e.getMessage());
		}

		File stderr = null;
		File stdout = null;
		
		if (output_file != null) {
			stderr = new File(output_file.getAbsolutePath() + ".stderr");
			stdout = new File(output_file.getAbsolutePath() + ".stdout");
		}
	
		io_threads[0] = new IOThread(stdout, p.getInputStream());
		io_threads[1] = new IOThread(stderr, p.getErrorStream());
		
		io_threads[0].start();
		io_threads[1].start();

		
		try {
			p.waitFor();
			io_threads[0].join();
			io_threads[1].join();
		} catch (InterruptedException e) {}
		
		int exit_code = p.exitValue();

		if (exit_code != 0) {
			TestCase.fail("Command \"" + sb.toString() + "\" failed: " + exit_code);
		}
	}

}

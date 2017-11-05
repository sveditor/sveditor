package net.sf.sveditor.core.builder;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class CoreBuildProcessListener implements ISVBuildProcessListener {

	private static class IOMonitorThread extends Thread {
		private InputStream			fIn;
		private boolean				fIsErr;
		
		public IOMonitorThread(InputStream in, boolean is_err) {
			fIn = in;
			fIsErr = is_err;
		}
		
		public void run() {
			InputStreamReader isr = new InputStreamReader(fIn);
			BufferedReader br = new BufferedReader(isr);
			String line;
		
			try {
				while ((line = br.readLine()) != null) {
					System.out.println(line);
				}
			} catch (IOException e) {
			}
		}
	}
	
	private static class ProcessMonitorThread extends Thread {
		private Process				fProcess;
		
		public ProcessMonitorThread(Process p) {
			fProcess = p;
		}
		
		public void run() {
			IOMonitorThread stdout = new IOMonitorThread(fProcess.getInputStream(), false);
			IOMonitorThread stderr = new IOMonitorThread(fProcess.getErrorStream(), true);
			
			stdout.start();
			stderr.start();
		
			try {
				stdout.join();
				stderr.join();
			
				fProcess.waitFor();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}

	@Override
	public void buildProcess(Process p) {
		ProcessMonitorThread t = new ProcessMonitorThread(p);
		t.start();
	}

}

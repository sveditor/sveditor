package net.sf.sveditor.core.script.launch;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.InputStreamLineReader;

public class ScriptRunner {

	private ILineListener			fOutLineListener = null;
	private ILineListener			fErrLineListener = null;
	
	public ScriptRunner() {
	}

	public void setOutLineListener(ILineListener l) {
		fOutLineListener = l;
	}
	
	public void setErrLineListener(ILineListener l) {
		fErrLineListener = l;
	}
	
	public Process start(
			IProgressMonitor	monitor,
			List<String>		arguments,
			Map<String, String>	env,
			File				working_dir) throws IOException {
		
		Map<String, String> sys_env = new HashMap<String, String>(System.getenv());
		
		if (env != null) {
			for (Entry<String, String> e : env.entrySet()) {
				if (sys_env.containsKey(e.getKey())) {
					sys_env.remove(e.getKey());
				}
				sys_env.put(e.getKey(), e.getValue());
			}
		}
		
		List<String> env_l = new ArrayList<String>();
		for (Entry<String, String> e : sys_env.entrySet()) {
			env_l.add(e.getKey() + "=" + e.getValue());
		}

		Process p = null;
		
		p = Runtime.getRuntime().exec(
				arguments.toArray(new String[arguments.size()]),
				env_l.toArray(new String[env_l.size()]),
				working_dir);
	
		return p;
	}	
	
	public int run(
			IProgressMonitor	monitor,
			List<String>		arguments,
			Map<String, String>	env,
			File				working_dir) throws IOException {
		
		Map<String, String> sys_env = new HashMap<String, String>(System.getenv());
		
		if (env != null) {
			for (Entry<String, String> e : env.entrySet()) {
				if (sys_env.containsKey(e.getKey())) {
					sys_env.remove(e.getKey());
				}
				sys_env.put(e.getKey(), e.getValue());
			}
		}
		
		List<String> env_l = new ArrayList<String>();
		for (Entry<String, String> e : sys_env.entrySet()) {
			env_l.add(e.getKey() + "=" + e.getValue());
		}

		Process p = null;
		
		p = Runtime.getRuntime().exec(
				arguments.toArray(new String[arguments.size()]),
				env_l.toArray(new String[env_l.size()]),
				working_dir);
	
		// Add listeners
		InputStreamLineReader out = new InputStreamLineReader(
				p.getInputStream(), new ILineListener() {
					public void line(String l) {
						if (fOutLineListener != null) {
							fOutLineListener.line(l);
						}
					}
				});
		
		InputStreamLineReader err = new InputStreamLineReader(
				p.getErrorStream(), new ILineListener() {
					public void line(String l) {
						if (fErrLineListener != null) {
							fErrLineListener.line(l);
						}
					}
				});
		out.start();
		err.start();
		
		int code = 0;
		
		long timeout = 1000/3;

		try {
			boolean done;
			do {
				done = p.waitFor(timeout, TimeUnit.MILLISECONDS);
				if (monitor.isCanceled()) {
					p.destroy();
				}
			} while (!done && !monitor.isCanceled());
			
			code = p.exitValue();
			
			// Cleanup
			out.join();
			err.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		return code;
	}
}

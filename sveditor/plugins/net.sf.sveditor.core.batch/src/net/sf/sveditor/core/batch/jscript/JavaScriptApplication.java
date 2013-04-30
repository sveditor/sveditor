package net.sf.sveditor.core.batch.jscript;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

import org.eclipse.core.runtime.Status;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

import sun.org.mozilla.javascript.NativeArray;

public class JavaScriptApplication implements IApplication {
	
	private void print_usage() {
		System.out.println("jscript [options] script.js [script_args]");
	}

	public Object start(IApplicationContext context) throws Exception {
		String script = null;
		List<String> scripts = new ArrayList<String>();
		List<String> script_args = new ArrayList<String>();
		String args[] = (String [])context.getArguments().get(IApplicationContext.APPLICATION_ARGS);
		
		for (int i=0; i<args.length; i++) {
			String arg = args[i];
			if (script == null) {
				if (arg.charAt(0) == '-') {
					if (arg.equals("-js")) {
						i++;
						arg = args[i];
						scripts.add(arg);
					} else {
						print_usage();
						throw new Exception("Unknown option " + arg);
					}
				} else {
					script = arg;
				}
			} else {
				script_args.add(arg);
			}
		}
	
		if (script == null) {
			print_usage();
			throw new Exception("script file not specified");
		}
		
		ScriptEngineManager mgr = new ScriptEngineManager();
		ScriptEngine eng = mgr.getEngineByName("JavaScript");

		// Set the command-line arguments
		List<String> argv = new ArrayList<String>();
		
		// Add the script path
		script_args.add(0, script);
		
		NativeArray arguments = new NativeArray(argv.toArray());
		
		eng.put("argv", argv);
		eng.put("arguments", arguments);
		
		scripts.add(script);
		
		for (String scr : scripts) {
			FileInputStream in = null;
			InputStreamReader reader = null;
			
			try {
				in = new FileInputStream(scr);
				reader = new InputStreamReader(in);
			} catch (IOException e) {
				print_usage();
				throw new Exception("Failed to open script " + scr);
			}

			try {
				eng.eval(reader);
			} catch (ScriptException e) {
				throw new Exception("Failure during script \"" + scr + "\" execution\n" + 
						e.getMessage());
			}
		}
		
		return Status.OK_STATUS;		
	}

	public void stop() {
		// TODO Auto-generated method stub

	}

}

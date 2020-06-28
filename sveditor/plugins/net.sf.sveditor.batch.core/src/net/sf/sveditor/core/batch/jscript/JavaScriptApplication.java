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
package net.sf.sveditor.core.batch.jscript;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.Status;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.mozilla.javascript.Context;
import org.mozilla.javascript.NativeArray;
import org.mozilla.javascript.Scriptable;
import org.mozilla.javascript.ScriptableObject;


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
	
		Context cx = Context.enter();
		Scriptable scope = cx.initStandardObjects();

		// Set the command-line arguments
		List<String> argv = new ArrayList<String>();
		
		// Add the script path
		script_args.add(0, script);
		
		NativeArray arguments = new NativeArray(argv.toArray());
		
		ScriptableObject.putProperty(scope, "arguments", arguments);
		
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
				cx.evaluateReader(scope, reader, scr, 1, null);
			} catch (IOException e) {
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

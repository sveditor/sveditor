/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.batch.python;

import java.util.Properties;

import org.eclipse.core.runtime.Status;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.python.core.PyDictionary;
import org.python.core.PyString;
import org.python.core.PySystemState;
import org.python.util.PythonInterpreter;

public class SVEditorPythonApplication implements IApplication {
	
	static boolean fInitialized;

	public Object start(IApplicationContext context) throws Exception {
		String args[] = (String [])context.getArguments().get(IApplicationContext.APPLICATION_ARGS);
		
		if (args.length < 1) {
			throw new Exception("script file not specified");
		}
		
		
		if (!fInitialized) {
			Properties p = new Properties();
			// p.setProperty("sys.path", value)
			PythonInterpreter.initialize(System.getProperties(), p, new String[]{});
			fInitialized = true;
		}
		
		PySystemState ss = new PySystemState();
		
		for (int i=0; i<args.length; i++) {
			ss.argv.add(new PyString(args[i]));
		}
		PyDictionary ls = new PyDictionary();
		
		PythonInterpreter interp = new PythonInterpreter(ls, ss);
		interp.execfile(args[0]);
		
		return Status.OK_STATUS;
	}

	public void stop() {
		// TODO Auto-generated method stub

	}

}

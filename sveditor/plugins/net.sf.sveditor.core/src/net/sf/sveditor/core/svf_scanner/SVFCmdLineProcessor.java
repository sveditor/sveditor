/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.svf_scanner;

import java.util.HashMap;
import java.util.Map;

public class SVFCmdLineProcessor {
	public static int					SWITCH_NO_ARGS      = 0;
	public static int					SWITCH_HAS_ARG      = 1;
	public static int					SWITCH_MAY_HAVE_ARG = 2;
	
	private Map<String, Integer>		fIgnoreSwitches;
	
	public SVFCmdLineProcessor() {
		fIgnoreSwitches = new HashMap<String, Integer>();
	}
	
	public void addIgnoreSwitch(String spec, int arg) {
		fIgnoreSwitches.put(spec, arg);
	}
	
	public StringBuilder process(String args[]) {
		StringBuilder cmdline = new StringBuilder();
		
		for (int i=0; i<args.length; i++) {
			String arg = args[i];
			
			if (arg.startsWith("-")) {
				
				for (String key : fIgnoreSwitches.keySet()) {
					if (arg.startsWith(key)) {
						
					}
				}
			}
		}
		
		return cmdline;
	}

}

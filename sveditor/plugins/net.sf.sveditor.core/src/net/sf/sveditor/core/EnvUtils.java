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
package net.sf.sveditor.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class EnvUtils {
	private	Map<String, String>			fEnv;
	
	public EnvUtils() {
		fEnv = new HashMap<String, String>();
		fEnv.putAll(System.getenv());
	}
	
	public void setenv(String var, String val) {
		if (fEnv.containsKey(var)) {
			fEnv.remove(var);
		}
		fEnv.put(var, val);
	}
	
	public void append(String var, String elem) {
		if (fEnv.containsKey(var)) {
			String val = fEnv.get(var);
			val = val + System.getProperty("path.separator") + elem;
			fEnv.remove(var);
			fEnv.put(var, val);
		} else {
			fEnv.put(var, elem);
		}
	}
	
	public void prepend(String var, String elem) {
		if (fEnv.containsKey(var)) {
			String val = fEnv.get(var);
			val = elem + System.getProperty("path.separator") + val;
			fEnv.remove(var);
			fEnv.put(var, val);
		} else {
			fEnv.put(var, elem);
		}
	}
	
	public String[] env() {
		List<String> env = new ArrayList<String>();
		
		for (Entry<String, String> e : fEnv.entrySet()) {
			env.add(e.getKey() + "=" + e.getValue());
		}
		
		return env.toArray(new String[env.size()]);
	}

}

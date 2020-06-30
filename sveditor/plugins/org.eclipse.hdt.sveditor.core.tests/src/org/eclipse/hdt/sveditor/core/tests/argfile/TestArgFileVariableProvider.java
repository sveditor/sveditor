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
package org.eclipse.hdt.sveditor.core.tests.argfile;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.argfile.parser.ISVArgFileVariableProvider;

public class TestArgFileVariableProvider implements
		ISVArgFileVariableProvider {
	private Map<String, String>				fVarMap;
	
	public TestArgFileVariableProvider() {
		fVarMap = new HashMap<String, String>();
	}
	
	public void setVar(String key, String val) {
		if (fVarMap.containsKey(key)) {
			fVarMap.remove(key);
		}
		fVarMap.put(key, val);
	}

	public boolean providesVar(String var) {
		System.out.println("providesVar: " + var);
		return fVarMap.containsKey(var);
	}

	public String expandVar(String var) {
		System.out.println("expandVar: " + var);
		return fVarMap.get(var);
	}

	public List<Tuple<String, String>> getRequestedVars() {
		return null;
	}

	public Set<String> getVariables() {
		return fVarMap.keySet();
	}
	
}

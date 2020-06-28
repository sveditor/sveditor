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
package org.eclipse.hdt.sveditor.core.argfile.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;

public class SVArgFileEnvVarProvider implements ISVArgFileVariableProvider {
	private List<Tuple<String, String>> 		fProvidedVars;
	
	public SVArgFileEnvVarProvider() {
		fProvidedVars = new ArrayList<Tuple<String,String>>();
	}

	public boolean providesVar(String var) {
		String val = SVCorePlugin.getenv(var);
		
		return (val != null);
	}

	public String expandVar(String var) {
		String val = SVCorePlugin.getenv(var);
		
		Tuple<String, String> t = new Tuple<String, String>(var, val);
		if (!fProvidedVars.contains(t)) {
			fProvidedVars.add(t);
		}
		
		return val;
	}

	public List<Tuple<String, String>> getRequestedVars() {
		return fProvidedVars;
	}

	public Set<String> getVariables() {
		return System.getenv().keySet();
	}

	
}

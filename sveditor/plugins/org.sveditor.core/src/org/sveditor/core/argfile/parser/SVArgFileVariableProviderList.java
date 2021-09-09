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
package org.sveditor.core.argfile.parser;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.sveditor.core.Tuple;

public class SVArgFileVariableProviderList implements
		ISVArgFileVariableProvider {
	
	private List<ISVArgFileVariableProvider>		fProviders;
	
	public SVArgFileVariableProviderList() {
		fProviders = new ArrayList<ISVArgFileVariableProvider>();
	}
	
	public void addProvider(ISVArgFileVariableProvider p) {
		fProviders.add(p);
	}

	public boolean providesVar(String var) {
		for (ISVArgFileVariableProvider p : fProviders) {
			if (p.providesVar(var)) {
				return true;
			}
		}

		return false;
	}

	public String expandVar(String var) {
		for (ISVArgFileVariableProvider p : fProviders) {
			if (p.providesVar(var)) {
				return p.expandVar(var);
			}
		}

		return null;
	}

	public List<Tuple<String, String>> getRequestedVars() {
		List<Tuple<String, String>> ret = new ArrayList<Tuple<String,String>>();

		for (ISVArgFileVariableProvider p : fProviders) {
			List<Tuple<String, String>> vl = p.getRequestedVars();
			for (Tuple<String, String> v : vl) {
				if (!ret.contains(v)) {
					ret.add(v);
				}
			}
		}
		
		return ret;
	}

	public Set<String> getVariables() {
		HashSet<String> ret = new HashSet<String>();
		
		for (ISVArgFileVariableProvider p : fProviders) {
			Set<String> vs = p.getVariables();
			for (String v : vs) {
				if (!ret.contains(v)) {
					ret.add(v);
				}
			}
		}
		
		return ret;
	}

	
}

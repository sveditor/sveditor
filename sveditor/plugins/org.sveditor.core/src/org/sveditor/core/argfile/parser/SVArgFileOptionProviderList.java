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
import java.util.List;

import org.sveditor.core.Tuple;

public class SVArgFileOptionProviderList implements ISVArgFileOptionProvider {
	private List<ISVArgFileOptionProvider>			fOptionProviders;
	
	public SVArgFileOptionProviderList() {
		fOptionProviders = new ArrayList<ISVArgFileOptionProvider>();
	}
	
	public void add(ISVArgFileOptionProvider p) {
		fOptionProviders.add(p);
	}
	
	public void remove(ISVArgFileOptionProvider p) {
		fOptionProviders.remove(p);
	}
	
	public List<String> getArgFilePaths(String option, String arg) {
		for (ISVArgFileOptionProvider p : fOptionProviders) {
			if (p.getOptionType(option) == OptionType.ArgFileInc) {
				return p.getArgFilePaths(option, arg);
			}
		}
		return null;
	}

	public OptionType getOptionType(String name) {
		OptionType type = OptionType.Unrecognized;
		for (ISVArgFileOptionProvider p : fOptionProviders) {
			OptionType tt = p.getOptionType(name);
			if (tt != OptionType.Unrecognized) {
				type = tt;
				break;
			}
		}
		
		return type;
	}

	public int optionArgCount(String name) {
		int count = -1;
		
		for (ISVArgFileOptionProvider p : fOptionProviders) {
			if (p.getOptionType(name) != OptionType.Unrecognized) {
				count = p.optionArgCount(name);
				break;
			}
		}
		
		return count;
	}

	public List<String> getIncPaths(String option, String arg) {
		List<String> inc_paths = null;
		
		for (ISVArgFileOptionProvider p : fOptionProviders) {
			if (p.getOptionType(option) == OptionType.Incdir) {
				inc_paths = p.getIncPaths(option, arg);
				break;
			}
		}
		
		return inc_paths;
	}

	public Tuple<String, String> getDefValue(String option, String arg) {
		Tuple<String, String> ret = null;

		for (ISVArgFileOptionProvider p : fOptionProviders) {
			if (p.getOptionType(option) == OptionType.Define) {
				ret = p.getDefValue(option, arg);
				break;
			}
		}

		return ret;
	}

}

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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.Tuple;

public class SVArgFileVCSOptionProvider implements ISVArgFileOptionProvider {
	
	private static Map<String, Integer>		fOptions;
	
	static {
		fOptions = new HashMap<String, Integer>(); 
	}

	public OptionType getOptionType(String name) {
		if (name.startsWith("+define+")) {
			return OptionType.Define;
		} else if (name.startsWith("+incdir+")) {
			return OptionType.Incdir;
		} else if (name.equals("-f")) {
			return OptionType.ArgFileInc;
		} else if (name.equals("-F")) {
			return OptionType.ArgFileRootInc;
		} else if (name.equals("-y")) {
			return OptionType.SrcLibPath;
		} else if (name.equals("-v")) {
			return OptionType.SrcLibFile;
		} else if (name.equals("-sverilog")) {
			return OptionType.SV;
		} else if (fOptions.containsKey(name)) {
			return OptionType.Ignored;
		} else {
			return OptionType.Unrecognized;
		}
	}

	public int optionArgCount(String name) {
		if (name.startsWith("+define+") ||
				name.startsWith("+incdir+")) {
			return 0;
		} else if (fOptions.containsKey(name)) {
			return fOptions.get(name);
		} else {		
			return 0;
		}		
	}
	
	public List<String> getArgFilePaths(String option, String arg) {
		List<String> ret = new ArrayList<String>();
		ret.add(arg);
		return ret;
	}

	public List<String> getIncPaths(String option, String arg) {
		List<String> ret = new ArrayList<String>();
		int idx = "+incdir+".length();
		int nidx;

			/*
		do {
			
		} while (nidx < )
		p = (option.indexOf('+', idx));
		if (kk)
		return null;
		 */
		return ret;
	}

	public Tuple<String, String> getDefValue(String option, String arg) {
		// TODO Auto-generated method stub
		return null;
	}

}

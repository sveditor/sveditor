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

import java.util.List;

import org.sveditor.core.Tuple;

public interface ISVArgFileOptionProvider {
	
	public enum OptionType {
		Unrecognized,
		Ignored,
		Incdir,
		Define,
		ArgFileInc,    		// -f path
		ArgFileRootInc, 	// -F path
		SrcLibPath, 		// -y <path>
		SrcLibFile,			// -v <file>
		SrcLibExt,			// +libext+.sv+.svh+.vlog
		MFCU,				// -mfcu
		SFCU,				// -sfcu
		SV,					// -sv or -sverilog
	}
	
	OptionType getOptionType(String name);
	
	int optionArgCount(String name);
	
	List<String> getArgFilePaths(String option, String arg);
	
	List<String> getIncPaths(String option, String arg);
	
	Tuple<String, String> getDefValue(String option, String arg);
	
//	List<String> getLibExts(String libext)

}

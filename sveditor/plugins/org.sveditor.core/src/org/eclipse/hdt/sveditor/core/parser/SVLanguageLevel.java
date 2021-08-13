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
package org.eclipse.hdt.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

public enum SVLanguageLevel {
	Verilog2005,
	
	VerilogAMS,
	
	// Default version of SystemVerilog
	SystemVerilog;
	

	public static final Set<String>			fVerilog2005Exts;
	public static final Set<String>			fVerilogAMSExts;
	
	static {
		fVerilog2005Exts = new HashSet<String>();
		fVerilog2005Exts.add(".v");
		fVerilog2005Exts.add(".vl");
		fVerilog2005Exts.add(".vlog");
		
		fVerilogAMSExts = new HashSet<String>();
		fVerilogAMSExts.add(".va");
		fVerilogAMSExts.add(".vams");
	}
	
	public static SVLanguageLevel computeLanguageLevel(String path) {
		String ext = null;
		
		int last_dot = path.lastIndexOf('.');
		
		if (last_dot != -1) {
			ext = path.substring(last_dot);
		}

		Boolean fileExtLangLevelOverride = 
			SVCorePlugin.getDefault().getFileExtLanguageLevelOverride() ;
		
		if (ext == null || fileExtLangLevelOverride) {
			return SystemVerilog;
		} else if (fVerilog2005Exts.contains(ext)) {
			return Verilog2005;
		} else if (fVerilogAMSExts.contains(ext)) {
			return VerilogAMS;
		} else {
			return SystemVerilog;
		}
	}
}

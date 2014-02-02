package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;

public enum SVLanguageLevel {
	Verilog2005,
	
	// Default version of SystemVerilog
	SystemVerilog;
	

	public static final Set<String>			fVerilog2005Exts;
	
	static {
		fVerilog2005Exts = new HashSet<String>();
		fVerilog2005Exts.add(".v");
		fVerilog2005Exts.add(".vl");
		fVerilog2005Exts.add(".vlog");
		
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
		} else {
			return SystemVerilog;
		}
	}
}

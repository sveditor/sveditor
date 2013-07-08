package net.sf.sveditor.core.argfile.parser;

import java.util.List;

import net.sf.sveditor.core.Tuple;

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
	}
	
	OptionType getOptionType(String name);
	
	int optionArgCount(String name);
	
	List<String> getArgFilePaths(String option, String arg);
	
	List<String> getIncPaths(String option, String arg);
	
	Tuple<String, String> getDefValue(String option, String arg);
	
//	List<String> getLibExts(String libext)

}

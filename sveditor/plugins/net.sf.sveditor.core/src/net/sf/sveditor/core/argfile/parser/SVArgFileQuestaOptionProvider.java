package net.sf.sveditor.core.argfile.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import net.sf.sveditor.core.Tuple;

public class SVArgFileQuestaOptionProvider implements ISVArgFileOptionProvider {
	
	private static HashMap<String, Integer>		fOptions;
	
	static {
		fOptions = new HashMap<String, Integer>();
		fOptions.put("-nowarn", 1);
		fOptions.put("-time", 0);
		fOptions.put("-version", 0);
		fOptions.put("-32", 0);
		fOptions.put("-64", 0);
		fOptions.put("-work", 1);
		fOptions.put("-error", 1);
		fOptions.put("-warning", 1);
		fOptions.put("-note", 1);
		fOptions.put("-suppress", 1);
		fOptions.put("-msglimit", 1);
		fOptions.put("-c", 0); // qverilog option
		fOptions.put("-compat", 0);
		fOptions.put("-ccflags", 1);
		fOptions.put("-compile_uselibs", 0);
		fOptions.put("-coveropt", 1);
		fOptions.put("-coverexcludedefault", 0);
		fOptions.put("-coverfec", 0);
		fOptions.put("-nocoverfec", 0);
		fOptions.put("-coverudp", 0);
		fOptions.put("-covershort", 0);
		fOptions.put("-nocoverexcludedefault", 0);
		fOptions.put("-covercells", 0);
		fOptions.put("-nocovercells", 0);
		fOptions.put("-constimmedassert", 0);
		fOptions.put("-togglecountlimit", 1);
		fOptions.put("-togglewidthlimit", 1);
		fOptions.put("-extendedtogglemode", 1);
		fOptions.put("-toggleportsonly", 0);
		fOptions.put("-maxudprows", 1);
		fOptions.put("-maxfecrows", 1);
		fOptions.put("-coverrportcancelleded", 0);
		fOptions.put("-deglitchalways", 0);
		fOptions.put("-dpiforceheader", 0);
		fOptions.put("-dpiheader", 1);
		fOptions.put("-do", 1); // qverilog option
		fOptions.put("-E", 1);
		fOptions.put("-Epretty", 1);
		fOptions.put("-Edebug", 1);
		fOptions.put("-enumfirstinit", 0);
		fOptions.put("-nofsmresettrans", 0);
		fOptions.put("-fsmresettrans", 0);
		fOptions.put("-nofsmsingle", 0);
		fOptions.put("-fsmsingle", 0);
		fOptions.put("-fsmimplicittrans", 0);
		fOptions.put("-nofsmimplicittrans", 0);
		fOptions.put("-fsmmultitrans", 0);
		fOptions.put("-fsmverbose", 1);
		fOptions.put("-nofsmxassign", 0);
		fOptions.put("-fsmxassign", 0);
		fOptions.put("-gen_xml", 2);
		fOptions.put("-hazards", 0);
		fOptions.put("-incr", 0);
		fOptions.put("-L", 1);
		fOptions.put("-Lf", 1);
		fOptions.put("-l", 1);
		fOptions.put("-libmap", 1);
		fOptions.put("-libmap_verbose", 0);
		fOptions.put("-line", 1);
		fOptions.put("-lint", 0);
		fOptions.put("-lowercasepragma", 0);
		fOptions.put("-lowercasepslpragma", 0);
		fOptions.put("-lrmclassinit", 0);
		fOptions.put("-modelsimini", 1);
		fOptions.put("-modelsimini", 1);
		fOptions.put("-mfcu", 0);
		fOptions.put("-nocheck", 0);
		fOptions.put("-nodebug", 0);
		fOptions.put("-nodbgsym", 0);
		fOptions.put("-noincr", 0);
		fOptions.put("-nologo", 0);
		fOptions.put("-nopsl", 0);
		fOptions.put("-novopt", 0);
		fOptions.put("-nowarn", 1);
		fOptions.put("-noconstimmedassert", 0);
		fOptions.put("-O0", 0);
		fOptions.put("-O1", 0);
		fOptions.put("-O4", 0);
		fOptions.put("-O5", 0);
		fOptions.put("-pedanticerrors", 0);
		fOptions.put("-permissive", 0);
		fOptions.put("-printinfilenames", 0);
		fOptions.put("-pslext", 0);
		fOptions.put("-pslfile", 1);
		fOptions.put("-quiet", 0);
		// skipping -R ... -
		fOptions.put("-refresh", 0);
		fOptions.put("-scdpiheader", 1);
		fOptions.put("-sfcu", 0);
		fOptions.put("-skipprotected", 0);
		fOptions.put("-skipprotectedmodule", 0);
		fOptions.put("-source", 0);
		fOptions.put("-sv", 0);
		fOptions.put("-sv05compat", 0);
		fOptions.put("-sv09compat", 0);
		fOptions.put("-oldsv", 0);
//		fOptions.put("-svimportport=", 0);
		fOptions.put("-timescale", 1);
		fOptions.put("-override_timescale", 1);
		fOptions.put("-u", 0);
		// TODO: handle -v switch ?
		fOptions.put("-v", 1);
		fOptions.put("-vlog96compat", 0);
		fOptions.put("-vlog01compat", 0);
		fOptions.put("-convertallparams", 0);
		fOptions.put("-mixedsvvh", 1);
		fOptions.put("-vopt", 0);
		fOptions.put("-vmake", 0);
		fOptions.put("-writetoplevels", 0);
//		fOptions.put("-y", 1);
		
		fOptions.put("+define+", 0);
		fOptions.put("+incdir+", 0);
		
		// Ignore for now
		fOptions.put("+libext+", 0);
		fOptions.put("-y", 1);
		fOptions.put("-v", 1);
		fOptions.put("-f", 1);
		fOptions.put("-F", 1);
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
		} else if (name.equals("-mfcu")) {
			return OptionType.MFCU;
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
		if (option.startsWith("+incdir+")) {
			List<String> ret = new ArrayList<String>();

			if (arg != null) {
				int last_plus = -1, next_plus = -1;
				do {
					next_plus = arg.indexOf('+', last_plus+1);

					if (next_plus != -1) {
						ret.add(arg.substring(last_plus+1, next_plus));
					} else {
						ret.add(arg.substring(last_plus+1));
					}
					last_plus = next_plus;
				} while (next_plus != -1);
			}
			return ret;
		} else {
			return null;
		}
	}

	public Tuple<String, String> getDefValue(String option, String arg) {
		int idx = arg.indexOf('=');
		String key=null, val=null;
		
		if (idx >= 0) {
			key = arg.substring(0, idx);
			val = arg.substring(idx+1, arg.length());
		} else {
			key = arg;
		}
		
		Tuple<String, String> ret = new Tuple<String, String>(key, val);
	
		return ret;
	}

	
}

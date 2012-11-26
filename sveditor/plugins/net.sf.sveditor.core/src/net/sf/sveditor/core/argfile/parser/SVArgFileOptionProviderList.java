package net.sf.sveditor.core.argfile.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;

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

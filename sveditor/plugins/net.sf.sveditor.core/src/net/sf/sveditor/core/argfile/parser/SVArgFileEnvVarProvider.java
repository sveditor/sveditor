package net.sf.sveditor.core.argfile.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;

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

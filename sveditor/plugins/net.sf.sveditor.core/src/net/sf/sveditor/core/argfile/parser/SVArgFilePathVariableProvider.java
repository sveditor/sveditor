package net.sf.sveditor.core.argfile.parser;

import java.net.URI;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.Tuple;

import org.eclipse.core.resources.IPathVariableManager;

public class SVArgFilePathVariableProvider implements
		ISVArgFileVariableProvider {
	private List<Tuple<String, String>>		fProvidedVars;
	private IPathVariableManager			fPathVariableManager;
	
	public SVArgFilePathVariableProvider(IPathVariableManager pvm) {
		fProvidedVars = new ArrayList<Tuple<String,String>>();
		fPathVariableManager = pvm;
	}

	public boolean providesVar(String var) {
		return (fPathVariableManager.getURIValue(var) != null);
	}

	public String expandVar(String var) {
		URI val = fPathVariableManager.getURIValue(var);
		
		if (val != null) {
			String ret = val.getPath();
			
			// TODO: may need to do some fixup
			
			Tuple<String, String> v = new Tuple<String, String>(var, ret);
			
			if (!fProvidedVars.contains(v)) {
				fProvidedVars.add(v);
			}
			
			return ret;
		} else {
			return null;
		}		
	}

	public List<Tuple<String, String>> getRequestedVars() {
		return fProvidedVars;
	}

	public Set<String> getVariables() {
		HashSet<String> ret = new HashSet<String>();
		
		for (String key : fPathVariableManager.getPathVariableNames()) {
			if (key.equals("WORKSPACE_LOC")) {
				ret.add("workspace_loc");
			} else {
				ret.add(key);
			}
		}
		
		return ret;
	}


}

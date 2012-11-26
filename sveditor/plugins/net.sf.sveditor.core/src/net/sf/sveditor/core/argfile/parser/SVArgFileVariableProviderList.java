package net.sf.sveditor.core.argfile.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;

public class SVArgFileVariableProviderList implements
		ISVArgFileVariableProvider {
	
	private List<ISVArgFileVariableProvider>		fProviders;
	
	public SVArgFileVariableProviderList() {
		fProviders = new ArrayList<ISVArgFileVariableProvider>();
	}
	
	public void addProvider(ISVArgFileVariableProvider p) {
		fProviders.add(p);
	}

	public boolean providesVar(String var) {
		for (ISVArgFileVariableProvider p : fProviders) {
			if (p.providesVar(var)) {
				return true;
			}
		}

		return false;
	}

	public String expandVar(String var) {
		for (ISVArgFileVariableProvider p : fProviders) {
			if (p.providesVar(var)) {
				return p.expandVar(var);
			}
		}

		return null;
	}

	public List<Tuple<String, String>> getRequestedVars() {
		List<Tuple<String, String>> ret = new ArrayList<Tuple<String,String>>();

		for (ISVArgFileVariableProvider p : fProviders) {
			List<Tuple<String, String>> vl = p.getRequestedVars();
			for (Tuple<String, String> v : vl) {
				if (!ret.contains(v)) {
					ret.add(v);
				}
			}
		}
		
		return ret;
	}

}

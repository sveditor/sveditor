package net.sf.sveditor.core.tests.argfile;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;

public class TestArgFileVariableProvider implements
		ISVArgFileVariableProvider {
	private Map<String, String>				fVarMap;
	
	public TestArgFileVariableProvider() {
		fVarMap = new HashMap<String, String>();
	}
	
	public void setVar(String key, String val) {
		if (fVarMap.containsKey(key)) {
			fVarMap.remove(key);
		}
		fVarMap.put(key, val);
	}

	public boolean providesVar(String var) {
		System.out.println("providesVar: " + var);
		return fVarMap.containsKey(var);
	}

	public String expandVar(String var) {
		System.out.println("expandVar: " + var);
		return fVarMap.get(var);
	}

	public List<Tuple<String, String>> getRequestedVars() {
		return null;
	}

	public Set<String> getVariables() {
		return fVarMap.keySet();
	}
	
}

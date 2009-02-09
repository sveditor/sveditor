package net.sf.sveditor.core.scanner;

import java.util.List;

public interface IDefineProvider {
	
//	String getDefineVal(String key, List<String> params);
	
	String expandMacro(String string, String filename, int lineno);
	
	boolean hasParameters(String key);

}

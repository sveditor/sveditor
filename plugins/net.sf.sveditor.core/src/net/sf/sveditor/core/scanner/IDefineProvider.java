package net.sf.sveditor.core.scanner;

import java.util.List;

public interface IDefineProvider {
	
	String getDefineVal(String key, List<String> params);
	
	boolean hasParameters(String key);

}

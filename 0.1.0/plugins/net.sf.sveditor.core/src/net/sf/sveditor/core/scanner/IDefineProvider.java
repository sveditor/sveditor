package net.sf.sveditor.core.scanner;


public interface IDefineProvider {
	
	String expandMacro(String string, String filename, int lineno);
	
	boolean isDefined(String name, int lineno);
	
	boolean hasParameters(String key);

}

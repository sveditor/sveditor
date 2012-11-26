package net.sf.sveditor.core.argfile.parser;

import java.util.List;

import net.sf.sveditor.core.Tuple;

public interface ISVArgFileVariableProvider {

	/**
	 * Returns true|false depending on whether the provider
	 * provides this variable
	 * 
	 * @param var
	 * @return
	 */
	boolean providesVar(String var);

	/**
	 * Expands variable 'var' and returns the expansion
	 * 
	 * @param var
	 * @return
	 */
	String expandVar(String var);

	/**
	 * Returns the list of variables requested by clients
	 * 
	 * @return
	 */
	List<Tuple<String, String>> getRequestedVars();

}

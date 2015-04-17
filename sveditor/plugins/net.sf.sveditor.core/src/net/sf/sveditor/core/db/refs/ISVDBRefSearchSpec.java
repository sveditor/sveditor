package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBItemBase;


public interface ISVDBRefSearchSpec {
	
	enum NameMatchType {
		Any,			// Ignore name
		Equals,
		MayContain		// Perform a quick search to see if there may be references
	}
	
	NameMatchType getNameMatchType();
	
	String getName();

	/**
	 * Check whether a given reference matches the spec
	 * 
	 * @param loc
	 * @param type
	 * @param scope
	 * @param name
	 * @return
	 */
	boolean matches(
			long 					loc, 
			SVDBRefType 			type, 
			Stack<ISVDBItemBase> 	scope, 
			String 					name);
	
}

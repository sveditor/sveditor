package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBItemBase;

public interface ISVDBRefFinderVisitor {

	void visitRef(
			long 						loc, 
			SVDBRefType 				type, 
			Stack<ISVDBItemBase>		scope_stack,
			String 						name);
	
}

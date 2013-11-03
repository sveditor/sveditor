package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBLocation;

public interface ISVDBRefFinderVisitor {

	void visitRef(
			SVDBLocation 				loc, 
			SVDBRefType 				type, 
			Stack<ISVDBChildItem>		scope_stack,
			String 						name);
	
}

package net.sf.sveditor.core.db.refs;

import java.util.Set;

import net.sf.sveditor.core.db.SVDBItemType;

public interface ISVDBRefSearchSpec {
	
	enum NameMatchType {
		Any,			// Ignore name
		Equals
	}
	
	NameMatchType getNameMatchType();
	
	String getName();
	
	Set<SVDBItemType> getTypes();

}

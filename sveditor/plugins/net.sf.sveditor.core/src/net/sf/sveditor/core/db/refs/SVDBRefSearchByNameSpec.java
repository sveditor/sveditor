package net.sf.sveditor.core.db.refs;

import java.util.Set;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBRefSearchByNameSpec implements ISVDBRefSearchSpec {
	private String					fName;
	
	public SVDBRefSearchByNameSpec(String name) {
		fName = name;
	}

	@Override
	public NameMatchType getNameMatchType() {
		return NameMatchType.Equals;
	}

	@Override
	public String getName() {
		return fName;
	}

	@Override
	public Set<SVDBItemType> getTypes() {
		return null;
	}

}

package net.sf.sveditor.core.db.refs;

import java.util.Set;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBRefSearchByNameSpec implements ISVDBRefSearchSpec {
	private String					fName;
	private NameMatchType			fMatchType;
	
	public SVDBRefSearchByNameSpec(String name, NameMatchType type) {
		fName = name;
		fMatchType = type;
	}
	
	public SVDBRefSearchByNameSpec(String name) {
		this(name, NameMatchType.Equals);
	}

	@Override
	public NameMatchType getNameMatchType() {
		return fMatchType;
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

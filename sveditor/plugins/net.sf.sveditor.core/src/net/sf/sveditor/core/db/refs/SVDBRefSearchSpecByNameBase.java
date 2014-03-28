package net.sf.sveditor.core.db.refs;


public abstract class SVDBRefSearchSpecByNameBase implements ISVDBRefSearchSpec {
	protected String					fName;
	protected NameMatchType			fMatchType;
	
	protected SVDBRefSearchSpecByNameBase(
			String 			name, 
			NameMatchType 	type) {
		fName = name;
		fMatchType = type;
	}
	
	@Override
	public NameMatchType getNameMatchType() {
		return fMatchType;
	}

	@Override
	public String getName() {
		return fName;
	}

}

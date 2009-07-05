package net.sf.sveditor.core.scanner;

import java.util.List;

public class SVTypeInfo {
	public boolean						fEnumType = false;
	public List<SVEnumVal>				fEnumVals;
	public String						fTypeName;
	public int							fTypeQualifiers;
	public List<SVClassIfcModParam>		fParameters;
	
}

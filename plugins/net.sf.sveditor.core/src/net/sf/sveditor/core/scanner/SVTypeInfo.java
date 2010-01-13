package net.sf.sveditor.core.scanner;

import java.util.List;

public class SVTypeInfo {
	public boolean						fEnumType 	= false;
	public boolean						fStructType = false;
	public boolean						fClassType  = false;
	public boolean						fModIfc   	= false;
	public List<SVEnumVal>				fEnumVals;
	public String						fTypeName;
	public String						fVectorDim;
	public int							fTypeQualifiers;
	public List<SVClassIfcModParam>		fParameters;
	
}

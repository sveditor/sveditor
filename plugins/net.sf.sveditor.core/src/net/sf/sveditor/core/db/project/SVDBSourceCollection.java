package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

public class SVDBSourceCollection {
	private String					fBaseLocation;
	private List<String>			fIncludes;
	private List<String>			fExcludes;
	
	public SVDBSourceCollection(String base_location) {
		fBaseLocation = base_location;
		fIncludes = new ArrayList<String>();
		fExcludes = new ArrayList<String>();
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public void setBaseLocation(String base) {
		fBaseLocation = base;
	}
	
	public List<String> getIncludes() {
		return fIncludes;
	}
	
	public List<String> getExcludes() {
		return fExcludes;
	}

	
	public SVDBSourceCollection duplicate() {
		SVDBSourceCollection ret = new SVDBSourceCollection(fBaseLocation);
		
		ret.getIncludes().addAll(fIncludes);
		ret.getExcludes().addAll(fExcludes);
		
		return ret;
	}
}

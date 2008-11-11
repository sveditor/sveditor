package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBModIfcClassDecl extends SVDBScopeItem {
	
	private List<SVDBModIfcClassParam>			fParams;
	
	public SVDBModIfcClassDecl(String name, SVDBItemType type) {
		super(name, type);
		
		fParams = new ArrayList<SVDBModIfcClassParam>();
	}
	
	public List<SVDBModIfcClassParam> getParameters() {
		return fParams;
	}
	
	public SVDBItem duplicate() {
		SVDBModIfcClassDecl ret = new SVDBModIfcClassDecl(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);

		fParams.clear();
		for (SVDBModIfcClassParam p : ((SVDBModIfcClassDecl)other).fParams) {
			fParams.add((SVDBModIfcClassParam)p.duplicate());
		}
	}
}

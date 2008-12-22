package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBModIfcClassDecl extends SVDBScopeItem {
	
	private List<SVDBModIfcClassParam>			fParams;
	private String								fSuperClass;
	private List<SVDBModIfcClassParam>			fSuperParams;
	
	public SVDBModIfcClassDecl(String name, SVDBItemType type) {
		super(name, type);
		
		fParams = new ArrayList<SVDBModIfcClassParam>();
		fSuperParams = new ArrayList<SVDBModIfcClassParam>();
	}
	
	public List<SVDBModIfcClassParam> getParameters() {
		return fParams;
	}
	
	public List<SVDBModIfcClassParam> getSuperParameters() {
		return fSuperParams;
	}
	
	public String getSuperClass() {
		return fSuperClass;
	}
	
	public void setSuperClass(String super_class) {
		fSuperClass = super_class;
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

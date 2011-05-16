package net.sf.sveditor.core.db;

public class SVDBProperty extends SVDBScopeItem {
	
	public SVDBProperty() {
		this("");
	}
	
	public SVDBProperty(String name) {
		super(name, SVDBItemType.Property);
	}

}

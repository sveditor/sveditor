package net.sf.sveditor.core.db;

public class SVDBSequence extends SVDBScopeItem {
	
	public SVDBSequence() {
		this("");
	}
	
	public SVDBSequence(String name) {
		super(name, SVDBItemType.Sequence);
	}

}

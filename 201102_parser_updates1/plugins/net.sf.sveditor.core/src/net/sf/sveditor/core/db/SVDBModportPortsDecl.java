package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBModportPortsDecl extends SVDBChildItem implements ISVDBAddChildItem {
	private List<ISVDBChildItem>			fPorts;
	
	protected SVDBModportPortsDecl(SVDBItemType type) {
		super(type);
		fPorts = new ArrayList<ISVDBChildItem>();
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fPorts.add(item);
	}
	
	public List<ISVDBChildItem> getPorts() {
		return fPorts;
	}
	
}

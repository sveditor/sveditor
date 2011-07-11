package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBModportItem extends SVDBItem {
	private List<SVDBModportPortsDecl>		fPorts;
	
	public SVDBModportItem() {
		this("");
	}
	
	public SVDBModportItem(String name) {
		super(name, SVDBItemType.ModportItem);
		fPorts = new ArrayList<SVDBModportPortsDecl>();
	}
	
	public List<SVDBModportPortsDecl> getPortsList() {
		return fPorts;
	}
	
	public void addPorts(SVDBModportPortsDecl p) {
		fPorts.add(p);
	}

}

package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBModportSimplePortsDecl extends SVDBModportPortsDecl {
	public enum PortDir {
		input,
		output,
		inout
	};
	private PortDir							fPortDir;
	private List<SVDBModportSimplePort>		fPortList;
	
	public SVDBModportSimplePortsDecl() {
		super(SVDBItemType.ModportSimplePortsDecl);
		fPortList = new ArrayList<SVDBModportSimplePort>();
	}
	
	public void setPortDir(PortDir dir) {
		fPortDir = dir;
	}
	
	public void setPortDir(String dir) {
		if (dir.equals("input")) {
			setPortDir(PortDir.input);
		} else if (dir.equals("output")) {
			setPortDir(PortDir.output);
		} else {
			setPortDir(PortDir.inout);
		}
	}
	
	public PortDir getPortDir() {
		return fPortDir;
	}
	
	public List<SVDBModportSimplePort> getPortList() {
		return fPortList;
	}
	
	public void addPort(SVDBModportSimplePort port) {
		fPortList.add(port);
	}

}

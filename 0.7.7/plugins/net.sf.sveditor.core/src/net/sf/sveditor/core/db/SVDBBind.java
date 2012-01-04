package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBBind extends SVDBChildItem implements ISVDBAddChildItem, ISVDBNamedItem {
	String			fTargetTypeName;
	List<String>	fTargetInstNameList;
	SVDBModIfcInst	fBindInst;
	
	public SVDBBind() {
		super(SVDBItemType.Bind);
		fTargetInstNameList = new ArrayList<String>();
	}
	
	public String getName() {
		return fTargetTypeName;
	}
	
	public void setTargetTypeName(String name) {
		fTargetTypeName = name;
	}
	
	public String getTargetTypeName() {
		return fTargetTypeName;
	}
	
	public List<String> getTargetInstNameList() {
		return fTargetInstNameList;
	}
	
	public void addTargetInstName(String name) {
		fTargetInstNameList.add(name);
	}
	
	public void setBindInst(SVDBModIfcInst inst) {
		fBindInst = inst;
	}
	
	public SVDBModIfcInst getBindInst() {
		return fBindInst;
	}

	public void addChildItem(ISVDBChildItem item) {
		if (item instanceof SVDBModIfcInst) {
			fBindInst = (SVDBModIfcInst)item;
		} else {
			fBindInst = null;
		}
	}
}

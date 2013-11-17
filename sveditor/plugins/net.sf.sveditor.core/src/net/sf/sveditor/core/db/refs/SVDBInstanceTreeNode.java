package net.sf.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBModuleDecl;

public class SVDBInstanceTreeNode {
	private SVDBInstanceTreeNode		fParent;
	private ISVDBItemBase				fItem;
	private List<SVDBInstanceTreeNode>	fInstantiations;
	
	public SVDBInstanceTreeNode(ISVDBItemBase item) {
		fParent = null;
		fItem = item;
		fInstantiations = new ArrayList<SVDBInstanceTreeNode>();
	}
	
	public String getTypename() {
		if (fItem.getType() == SVDBItemType.ModuleDecl) {
			return ((SVDBModuleDecl)fItem).getName();
		} else if (fItem.getType() == SVDBItemType.ModIfcInstItem) {
			SVDBModIfcInst inst = (SVDBModIfcInst)((SVDBModIfcInstItem)fItem).getParent();
			return inst.getTypeName();
		} else {
			return null;
		}
	}
	
	public String getInstname() {
		if (fItem.getType() == SVDBItemType.ModIfcInstItem) {
			return ((SVDBModIfcInstItem)fItem).getName();
		}
		return null;
	}
	
	public List<SVDBInstanceTreeNode> getInstantiations() {
		return fInstantiations;
	}
	
	public SVDBInstanceTreeNode getParent() {
		return fParent;
	}
	
	public void setParent(SVDBInstanceTreeNode p) {
		fParent = p;
	}
	
	public void addInstantiation(SVDBInstanceTreeNode inst) {
		inst.setParent(this);
		fInstantiations.add(inst);
	}
	

}

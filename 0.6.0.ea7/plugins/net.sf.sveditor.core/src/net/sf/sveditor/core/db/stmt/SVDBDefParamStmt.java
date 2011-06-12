package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBDefParamStmt extends SVDBStmt {
	private List<SVDBDefParamItem>		fParamAssignList;
	
	public SVDBDefParamStmt() {
		super(SVDBItemType.DefParamStmt);
		fParamAssignList = new ArrayList<SVDBDefParamItem>();
	}
	
	public List<SVDBDefParamItem> getParamAssignList() {
		return fParamAssignList;
	}
	
	public void addParamAssign(SVDBDefParamItem item) {
		fParamAssignList.add(item);
	}

}

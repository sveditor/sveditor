package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBRandseqStmt extends SVDBStmt {
	
	public String							fName;
	public List<SVDBParamPortDecl>			fParams;
	public List<SVDBRandseqProdStmt>		fRandseqProdStmtList;

	public SVDBRandseqStmt() {
		super(SVDBItemType.RandseqStmt);
		fParams = new ArrayList<SVDBParamPortDecl>();
		fRandseqProdStmtList = new ArrayList<SVDBRandseqProdStmt>();
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void addRandseqProdStmt (SVDBRandseqProdStmt item)  {
		fRandseqProdStmtList.add(item);
	}
	
	
	public void setTfPortList(List<SVDBParamPortDecl> params) {
		fParams = params;
		if (params != null)  {
			for (SVDBParamPortDecl p : params) {
				p.setParent(this);
			}
		}
	}
	

}

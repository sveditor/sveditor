package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBRandseqProdStmt extends SVDBStmt {
	public SVDBTypeInfo				fRetType;
	public String					fName;
	public List<SVDBParamPortDecl>	fPortList;
	public List<SVDBExpr>			fExprList;
	
	public SVDBRandseqProdStmt() {
		super(SVDBItemType.RandseqProdStmt);
		fExprList = new ArrayList<SVDBExpr>();
		fPortList   = new ArrayList<SVDBParamPortDecl>();
	}
	
	public void setRetType(SVDBTypeInfo type) {
		fRetType = type;
	}
	
	public SVDBTypeInfo getRetType() {
		return fRetType;
	}

	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void addProductionItem(SVDBExpr pi) {
		fExprList.add(pi);
	}
	
	
	public List<SVDBExpr> getProductionItemList() {
		return fExprList;
	}
	
	
	public void setTfPortList(List<SVDBParamPortDecl> params) {
		fPortList = params;
		if (params != null)  {
			for (SVDBParamPortDecl p : params) {
				p.setParent(this);
			}
		}
	}
	
	public List<SVDBParamPortDecl> getTfPortList() {
		return fPortList;
	}
	



}

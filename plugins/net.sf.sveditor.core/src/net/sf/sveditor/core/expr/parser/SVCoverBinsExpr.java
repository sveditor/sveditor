package net.sf.sveditor.core.expr.parser;

import java.util.ArrayList;
import java.util.List;

public class SVCoverBinsExpr extends SVCoverageExpr {
	private String				fName;
	private String				fBinsType;
	private boolean				fIsArray;
	private SVExpr				fArrayExpr;
	private List<SVExpr>		fRangeList;
	private boolean				fIsDefault;
	
	public SVCoverBinsExpr(String name, String bins_type) {
		super(SVExprType.CoverBins);
		fName 			= name;
		fBinsType 		= bins_type;
		fRangeList  	= new ArrayList<SVExpr>();
	}
	
	public String getName() {
		return fName;
	}
	
	public void setIsDefault(boolean dflt) {
		fIsDefault = dflt;
	}
	
	public boolean isDefault() {
		return fIsDefault;
	}
	
	public String getBinsType() {
		return fBinsType;
	}
	
	public boolean isArray() {
		return fIsArray;
	}
	
	public void setIsArray(boolean is_array) {
		fIsArray = is_array;
	}
	
	public SVExpr getArrayExpr() {
		return fArrayExpr;
	}
	
	public void setArrayExpr(SVExpr expr) {
		fArrayExpr = expr;
	}
	
	public List<SVExpr> getRangeList() {
		return fRangeList;
	}
	

}

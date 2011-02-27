package net.sf.sveditor.core.db;

import java.util.List;

import net.sf.sveditor.core.db.SVDBCoverGroup.BinsKW;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBCoverpointBins extends SVDBItem {
	public enum BinsType {
		OpenRangeList,
		TransList,
		Default,
		DefaultSeq
	};
	
	
	private boolean					fWildcard;
	private BinsKW					fBinsKW;
	private BinsType				fBinsType;
	private boolean					fIsArray;
	private SVExpr					fArrayExpr;
	private SVExpr					fIFF;
	
	private List<SVExpr>			fRangeList;
	
	public SVDBCoverpointBins(boolean wildcard, String name, BinsKW kw) {
		super(name, SVDBItemType.CoverpointBins);
		fWildcard = wildcard;
		fBinsKW = kw;
	}
	
	public void setIsWildcard(boolean wildcard) {
		fWildcard = wildcard;
	}
	
	public boolean isWildcard() {
		return fWildcard;
	}
	
	public BinsKW getBinsKW() {
		return fBinsKW;
	}
	
	public void setBinsKW(BinsKW kw) {
		fBinsKW = kw;
	}
	
	public void setIsArray(boolean is_array) {
		fIsArray = is_array;
	}
	
	public boolean isArray() {
		return fIsArray;
	}
	
	public SVExpr getArrayExpr() {
		return fArrayExpr;
	}
	
	public void setArrayExpr(SVExpr expr) {
		fArrayExpr = expr;
	}
	
	public void setBinsType(BinsType type) {
		fBinsType = type;
	}
	
	public BinsType getBinsType() {
		return fBinsType;
	}
	
	public SVExpr getIFF() {
		return fIFF;
	}
	
	public void setIFF(SVExpr expr) {
		fIFF = expr;
	}
	
}

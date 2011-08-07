package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVDBExpr;

/**
 * Holds type information about an array field or typedef
 * 
 * @author ballance
 *
 */
public class SVDBVarDimItem extends SVDBStmt {
	
	public enum DimType {
		Unsized,
		Sized,
		Associative,
		Queue
	};
	
	private DimType					fDimType;
	// Used for unpacked_dimension, packed_dimension, queue_dimension (when upper bound specified)
	private SVDBExpr				fExpr;
	// Used for associative_dimension when a type is specified
	private SVDBTypeInfo			fTypeInfo;

	public SVDBVarDimItem() {
		super(SVDBItemType.VarDimItem);
	}
	
	public void setDimType(DimType type) {
		fDimType = type;
	}

	public DimType getDimType() {
		return fDimType; 
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public void setTypeInfo(SVDBTypeInfo type_info) {
		fTypeInfo = type_info;
	}

}

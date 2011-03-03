package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

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
	private SVExpr					fExpr;
	// Used for associative_dimension when a type is specified
	private SVDBTypeInfo			fTypeInfo;

	public static void init() {
		SVDBPersistenceReader.registerEnumType(DimType.class, DimType.values());
		SVDBPersistenceReader.registerPersistenceFactory(new ISVDBPersistenceFactory() {
			
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type,
					IDBReader reader) throws DBFormatException {
				return new SVDBVarDimItem(parent, type, reader);
			}
		}, SVDBItemType.VarDimItem);
	}
	
	public SVDBVarDimItem() {
		super(SVDBItemType.VarDimItem);
	}
	
	public SVDBVarDimItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		fDimType = (DimType)reader.readEnumType(DimType.class);
		
		if (fDimType == DimType.Associative) {
			fTypeInfo = (SVDBTypeInfo)reader.readSVDBItem(this);
		} else {
			fExpr = SVExpr.readExpr(reader);
		}
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeEnumType(DimType.class, fDimType);
		
		if (fDimType == DimType.Associative) {
			writer.writeSVDBItem(fTypeInfo);
		} else {
			SVExpr.writeExpr(fExpr, writer);
		}
	}
	
	public void setDimType(DimType type) {
		fDimType = type;
	}

	public DimType getDimType() {
		return fDimType; 
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public void setTypeInfo(SVDBTypeInfo type_info) {
		fTypeInfo = type_info;
	}

}

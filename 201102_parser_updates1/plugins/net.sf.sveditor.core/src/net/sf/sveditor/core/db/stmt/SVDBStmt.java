package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBStmt extends SVDBChildItem {
	
	public static void init() {
		SVDBAlwaysStmt.init();
		SVDBForStmt.init();
		SVDBVarDeclStmt.init();
		SVDBParamPort.init();
	}
	
	public static SVDBStmt readStmt(ISVDBChildItem parent, IDBReader reader) throws DBFormatException {
		ISVDBItemBase item = reader.readSVDBItem(parent);
		
		if (item == null) {
			return null;
		} else if (!(item instanceof SVDBStmt)) {
			throw new DBFormatException("Error reading statement: type=" + item.getType());
		}
		return (SVDBStmt)item;
	}
	
	public static void writeStmt(SVDBStmt stmt, IDBWriter writer) {
		if (stmt == null) {
			writer.writeItemType(SVDBItemType.NULL);
		} else {
			stmt.dump(writer);
		}
	}
	
	public SVDBStmt(SVDBItemType type) {
		super(type);
	}
	
	public SVDBStmt(ISVDBItemBase parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(type);
		fLocation = new SVDBLocation(reader.readInt(), reader.readInt());
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeInt((fLocation != null)?fLocation.getLine():0);
		writer.writeInt((fLocation != null)?fLocation.getPos():0);
	}
	
	@Override
	public SVDBStmt duplicate() {
		SVDBStmt ret = new SVDBStmt(getType());
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
	}

	@Override
	public boolean equals(Object obj) {
		// TODO Auto-generated method stub
		return super.equals(obj);
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		// TODO Auto-generated method stub
		return super.equals(obj, full);
	}
	
	public static boolean isType(ISVDBItemBase item, SVDBItemType ... types) {
		// TODO: item.itemClass() == SVDBItemClass.Stmt
		boolean ret = true;
		
		if (ret) {
			ret = false;
			for (SVDBItemType t : types) {
				if (t == item.getType()) {
					ret = true;
					break;
				}
			}
		}
		
		return ret;
	}
	
}

package net.sf.sveditor.core.db.stmt;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBChildItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBStmt extends SVDBChildItem {
	private SVDBStmtType		fStmtType;
	private static Map<SVDBStmtType, ISVDBStmtPersistenceFactory>	fPersistenceMap;
	
	static {
		fPersistenceMap = new HashMap<SVDBStmtType, ISVDBStmtPersistenceFactory>();
	}
	
	public static void init() {
		SVDBPersistenceReader.registerEnumType(SVDBStmtType.class, SVDBStmtType.values());
		
		SVDBPersistenceReader.registerPersistenceFactory(new ISVDBPersistenceFactory() {
			
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type,
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				SVDBStmtType stmt_type = (SVDBStmtType)reader.readEnumType(SVDBStmtType.class);
				
				return readStmt(parent, stmt_type, reader);
			}
		}, SVDBItemType.Stmt);
		
		SVDBForStmt.init();
		SVDBVarDeclStmt.init();
		SVDBParamPort.init();
	}
	
	private static SVDBStmt readStmt(ISVDBChildItem parent, SVDBStmtType stmt_type, IDBReader reader) throws DBFormatException {

		ISVDBStmtPersistenceFactory f = fPersistenceMap.get(stmt_type);
		
		if (f == null) {
			throw new DBFormatException("No persistence factory registered for Statement " + stmt_type);
		}
		
		return f.readSVDBStmt(parent, stmt_type, reader);
	}
	
	public static SVDBStmt readStmt(ISVDBChildItem parent, IDBReader reader) throws DBFormatException {
		SVDBItemType type = reader.readItemType();
		
		if (type == SVDBItemType.NULL) {
			return null;
		} else {
			if (type != SVDBItemType.Stmt) {
				throw new DBFormatException("Error reading statement: type=" + type);
			}
			SVDBStmtType stmt_type = (SVDBStmtType)reader.readEnumType(SVDBStmtType.class);
			return readStmt(parent, stmt_type, reader);
		}
	}
	
	public static void writeStmt(SVDBStmt stmt, IDBWriter writer) {
		if (stmt == null) {
			writer.writeItemType(SVDBItemType.NULL);
		} else {
			stmt.dump(writer);
		}
	}
	
	public static void registerPersistenceFactory(ISVDBStmtPersistenceFactory f, SVDBStmtType ... stmt_types) {
		for (SVDBStmtType t : stmt_types) {
			fPersistenceMap.put(t, f);
		}
	}
	
	public SVDBStmt(SVDBStmtType type) {
		super(SVDBItemType.Stmt);
		fStmtType = type;
	}
	
	public SVDBStmt(ISVDBItemBase parent, SVDBStmtType stmt_type, IDBReader reader) throws DBFormatException {
		super(SVDBItemType.Stmt);
		fStmtType = stmt_type;
		fLocation = new SVDBLocation(reader.readInt(), reader.readInt());
	}
	
	public SVDBStmtType getStmtType() {
		return fStmtType;
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeEnumType(SVDBStmtType.class, fStmtType);
		writer.writeInt((fLocation != null)?fLocation.getLine():0);
		writer.writeInt((fLocation != null)?fLocation.getPos():0);
	}
	
	@Override
	public SVDBStmt duplicate() {
		SVDBStmt ret = new SVDBStmt(fStmtType);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
		SVDBStmt o = (SVDBStmt)other;
		
		fStmtType = o.fStmtType;
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
	
	public static boolean isType(ISVDBItemBase item, SVDBStmtType ... types) {
		boolean ret = (item.getType() == SVDBItemType.Stmt);
		
		if (ret) {
			SVDBStmt stmt = (SVDBStmt)item;
			ret = false;
			for (SVDBStmtType t : types) {
				if (t == stmt.getStmtType()) {
					ret = true;
					break;
				}
			}
		}
		
		return ret;
	}
	
}

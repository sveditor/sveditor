package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBBlockStmt extends SVDBStmt /* implements ISVDBScopeItem  */{
	private ISVDBChildItem			fParent;
	private List<ISVDBItemBase>		fItems;
	private SVDBLocation			fEndLocation;
	private String					fBlockName;
	
	public static void init() {
		SVDBStmt.registerPersistenceFactory(new ISVDBStmtPersistenceFactory() {
			public SVDBStmt readSVDBStmt(ISVDBChildItem parent, SVDBStmtType type,
					IDBReader reader) throws DBFormatException {
				return new SVDBBlockStmt(parent, type, reader);
			}
		}, SVDBStmtType.Block);
	}
	
	public SVDBBlockStmt() {
		super(SVDBStmtType.Block);
		fBlockName = "";
		fItems = new ArrayList<ISVDBItemBase>();
	}
	
	public SVDBBlockStmt(ISVDBChildItem parent, SVDBStmtType type, IDBReader reader) 
		throws DBFormatException {
		super(parent, type, reader);
		fParent = parent;
		
		fBlockName = reader.readString();
		fEndLocation = SVDBLocation.readLocation(reader);
		// TODO: 
		fItems = new ArrayList<ISVDBItemBase>();
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fBlockName);
		SVDBLocation.writeLocation(fEndLocation, writer);
	}
	
	public void addStmt(SVDBStmt stmt) {
		fItems.add(stmt);
	}
	
	public String getBlockName() {
		return fBlockName;
	}
	
	public void setBlockName(String name) {
		fBlockName = name;
	}

	public ISVDBChildItem getParent() {
		return fParent;
	}

	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}

	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}

	public List<ISVDBItemBase> getItems() {
		return fItems;
	}

	@Override
	public SVDBBlockStmt duplicate() {
		SVDBBlockStmt ret = new SVDBBlockStmt();
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(ISVDBItemBase other) {
		SVDBBlockStmt o = (SVDBBlockStmt)other;
		super.init(other);
		
		fBlockName = o.getBlockName();
		if (o.getEndLocation() == null) {
			fEndLocation = null;
		} else {
			fEndLocation = o.getEndLocation().duplicate();
		}
		fItems.clear();
		for (ISVDBItemBase i : o.getItems()) {
			fItems.add(i.duplicate());
		}
		fParent = o.getParent();
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		if (!super.equals(obj, full)) {
			return false;
		}
		
		boolean ret = true;
		
		// TODO:
		
		return ret;
	}

	
}

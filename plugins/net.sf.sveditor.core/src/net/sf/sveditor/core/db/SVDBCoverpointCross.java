package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBCoverpointCross extends SVDBItem {
	private List<String>		fCoverpointList;
	private String				fBody;

	public SVDBCoverpointCross(String name, String body) {
		super(name, SVDBItemType.CoverpointCross);
		fBody = body;
		fCoverpointList = new ArrayList<String>();
	}

	public List<String> getCoverpointList() {
		return fCoverpointList;
	}
	
	public SVDBCoverpointCross(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) 
		throws DBFormatException {
		super(file, parent, type, reader);

		fBody = reader.readString();
		fCoverpointList = reader.readStringList();
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);

		writer.writeString(fBody);
		writer.writeStringList(fCoverpointList);
	}

	@Override
	public SVDBItem duplicate() {
		SVDBCoverpointCross ret = new SVDBCoverpointCross(getName(), fBody);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		SVDBCoverpointCross other_i = (SVDBCoverpointCross)other;
		
		super.init(other);
		
		fCoverpointList.clear();
		fCoverpointList.addAll(other_i.fCoverpointList);
	}

}

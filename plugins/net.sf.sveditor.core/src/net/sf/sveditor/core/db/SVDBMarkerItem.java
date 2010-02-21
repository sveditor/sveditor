package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBMarkerItem extends SVDBItem {
	
	public static final String			MARKER_ERR = "ERROR";
	
	private String				fMessage;
	
	public SVDBMarkerItem(String name, String message) {
		super(name, SVDBItemType.Marker);
		fMessage = message;
	}
	
	public SVDBMarkerItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fMessage = reader.readString();
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fMessage);
	}

	public void setMessage(String msg) {
		fMessage = msg;
	}
	
	public String getMessage() {
		return fMessage;
	}

	@Override
	public SVDBItem duplicate() {
		SVDBMarkerItem ret = new SVDBMarkerItem(getName(), getMessage());
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		SVDBMarkerItem m = (SVDBMarkerItem)other;
		
		super.init(other);
		
		fMessage = m.fMessage; 
	}
	
}

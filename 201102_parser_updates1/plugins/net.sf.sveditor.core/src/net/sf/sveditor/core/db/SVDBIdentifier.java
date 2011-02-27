package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParseException;

public class SVDBIdentifier extends SVDBItemBase {
	private String				fId;
	
	public static void init() {
		SVDBPersistenceReader.registerPersistenceFactory(new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(
					ISVDBChildItem parent, SVDBItemType type, IDBReader reader
					) throws DBFormatException {
				return new SVDBIdentifier(parent, type, reader);
			}
		}, SVDBItemType.Id);
	}
	
	public SVDBIdentifier(String id, SVDBLocation loc) {
		super(SVDBItemType.Id);
		fId = id;
		setLocation(loc);
	}
	
	public SVDBIdentifier(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		fId = reader.readString();
	}
	
	public String getId() {
		return fId;
	}
	
	public static SVDBIdentifier readId(IDBReader reader) throws DBFormatException {
		String id = reader.readString();
		SVDBLocation loc = SVDBLocation.readLocation(reader);
		
		return new SVDBIdentifier(id, loc);
	}
	
	public static void writeId(SVDBIdentifier id, IDBWriter writer) {
		writer.writeString(id.getId());
		SVDBLocation.writeLocation(id.getLocation(), writer);
	}

	public static SVDBIdentifier readId(SVLexer lexer) throws SVParseException {
		SVDBLocation loc = lexer.getStartLocation();
		String id = lexer.readId();
		
		return new SVDBIdentifier(id, loc);
	}
	

}

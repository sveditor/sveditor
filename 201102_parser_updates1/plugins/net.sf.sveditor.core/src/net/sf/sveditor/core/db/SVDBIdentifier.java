package net.sf.sveditor.core.db;

import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParseException;


public class SVDBIdentifier extends SVDBItemBase {
	private String				fId;

	public SVDBIdentifier() {
		super(SVDBItemType.Identifier);
	}
	
	public SVDBIdentifier(String id, SVDBLocation loc) {
		super(SVDBItemType.Identifier);
		fId = id;
		setLocation(loc);
	}
	
	public String getId() {
		return fId;
	}
	
	public static SVDBIdentifier readId(SVLexer lexer) throws SVParseException {
		SVDBLocation start = lexer.getStartLocation();
		SVDBIdentifier ret = new SVDBIdentifier(lexer.readId(), start);
		
		return ret;
	}
	
}

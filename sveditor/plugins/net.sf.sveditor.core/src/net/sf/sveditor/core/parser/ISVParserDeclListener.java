package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBItemBase;

public interface ISVParserDeclListener {
	
	void enter_type_scope(ISVDBItemBase item);
	
	void declaration(ISVDBItemBase item);
	
	void leave_type_scope(ISVDBItemBase item);

}

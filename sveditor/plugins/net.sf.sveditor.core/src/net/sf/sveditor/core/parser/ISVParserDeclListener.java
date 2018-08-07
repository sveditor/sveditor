package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBItemBase;

public interface ISVParserTypeListener {
	
	void enter_type_scope(ISVDBItemBase item);
	
	void leave_type_scope(ISVDBItemBase item);

}

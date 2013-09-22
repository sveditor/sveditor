package net.sf.sveditor.vhdl.core.db.index;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

public class VhdlArgFileIndexFactory implements ISVDBIndexFactory {
	
	public static final String					TYPE = "net.sf.sveditor.vhdl.argFileIndex";

	public VhdlArgFileIndexFactory() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public ISVDBIndex createSVDBIndex(
			String project_name,
			String base_location, 
			ISVDBIndexCache cache, 
			SVDBIndexConfig config) {
		// TODO Auto-generated method stub
		return null;
	}

}

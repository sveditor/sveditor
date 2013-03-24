package net.sf.sveditor.core.argfile.filter;

import net.sf.sveditor.core.db.SVDBFile;

public interface IArgFileFilter {
	
	public SVDBFile filter(SVDBFile in);

}

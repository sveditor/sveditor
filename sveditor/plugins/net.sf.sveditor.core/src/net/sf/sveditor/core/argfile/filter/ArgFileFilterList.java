package net.sf.sveditor.core.argfile.filter;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;

public class ArgFileFilterList implements IArgFileFilter {
	private List<IArgFileFilter>		fFilterList;
	
	public ArgFileFilterList() {
		fFilterList = new ArrayList<IArgFileFilter>();
	}
	
	public void addFilter(IArgFileFilter filter) {
		fFilterList.add(filter);
	}

	public SVDBFile filter(SVDBFile in) {
		for (IArgFileFilter f : fFilterList) {
			in = f.filter(in);
		}
		
		return in;
	}

}

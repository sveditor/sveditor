package net.sf.sveditor.core.argfile.filter;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBFile;

public class ArgFileFilterOptionsFirst implements IArgFileFilter {

	public SVDBFile filter(SVDBFile in) {
		List<ISVDBChildItem> options = new ArrayList<ISVDBChildItem>();
		List<ISVDBChildItem> arguments = new ArrayList<ISVDBChildItem>();
		
		for (ISVDBChildItem it : in.getChildren()) {
			switch (it.getType()) {
				case ArgFileIncDirStmt:
				case ArgFileLibExtStmt:
				case ArgFileDefineStmt: {
					options.add(it);
				} break;
				
				default: {
					arguments.add(it);
				} break;
			}
		}
	
		SVDBFile ret = new SVDBFile(in.getFilePath());
		
		for (ISVDBChildItem it : options) {
			ret.addChildItem(it);
		}
		
		for (ISVDBChildItem it : arguments) {
			ret.addChildItem(it);
		}
		// TODO Auto-generated method stub
		
		return ret;
	}

}

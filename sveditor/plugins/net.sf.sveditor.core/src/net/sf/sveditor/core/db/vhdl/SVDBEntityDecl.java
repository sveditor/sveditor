package net.sf.sveditor.core.db.vhdl;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBEntityDecl extends SVDBScopeItem {
	
	public SVDBEntityDecl(String name) {
//		super(name, SVDBItemType.VHEntityDecl);
		super(name, SVDBItemType.ModuleDecl);
	}

}

package net.sf.sveditor.core.expr_utils;

import net.sf.sveditor.core.db.ISVDBItemBase;

public interface ISVItemResolver {
	
	ISVDBItemBase resolveItemScopeRelative(String name);
	
	ISVDBItemBase resolveItemBaseRelative(ISVDBItemBase base, String name);

}

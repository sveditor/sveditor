package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;


/**
 * Finds references to modules or interfaces
 * 
 * @author ballance
 *
 */
public class SVDBRefSearchSpecModIfcRefsByName extends SVDBRefSearchSpecByNameBase {
	
	public SVDBRefSearchSpecModIfcRefsByName(String name) {
		super(name, NameMatchType.Equals);
	}
	
	public SVDBRefSearchSpecModIfcRefsByName(String name, NameMatchType type) {
		super(name, type);
	}


	@Override
	public boolean matches(
			long		 			loc, 
			SVDBRefType 			type,
			Stack<ISVDBItemBase> 	scope, 
			String 					name) {
		if (scope.peek().getType() == SVDBItemType.ModIfcInst) {
			switch (fMatchType) {
				case MayContain:
				case Any: return true;
				case Equals: return fName.equals(name);
			}
		}
			
		return false;
	}

}

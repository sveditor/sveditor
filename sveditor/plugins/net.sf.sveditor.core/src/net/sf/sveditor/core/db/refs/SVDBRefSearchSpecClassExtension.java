package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBRefSearchSpecClassExtension extends
		SVDBRefSearchSpecByNameBase {
	private SVDBClassDecl			fCls;
	
	public SVDBRefSearchSpecClassExtension(SVDBClassDecl cls) {
		super(cls.getName(), NameMatchType.Equals);
		fCls = cls;
	}

	@Override
	public boolean matches(
			long		 			loc, 
			SVDBRefType 			type,
			Stack<ISVDBItemBase> 	scope, 
			String 					name) {
		if (scope.peek().getType() == SVDBItemType.ClassDecl) {
			SVDBClassDecl cls = (SVDBClassDecl)scope.peek();
			if (cls.getSuperClass() != null &&
					cls.getSuperClass().getName() != null &&
					fCls != null && fCls.getName() != null &&
					cls.getSuperClass().getName().equals(fCls.getName())) {
				return true;
			}
		}

		return false;
	}

}

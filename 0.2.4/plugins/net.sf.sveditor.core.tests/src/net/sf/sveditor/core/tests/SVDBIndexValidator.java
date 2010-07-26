package net.sf.sveditor.core.tests;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class SVDBIndexValidator extends TestCase {
	public static final int					ExpectErrors = (1 << 0);
	
	public void validateIndex(ISVDBItemIterator<SVDBItem> i_it, int flags) {
		
		while (i_it.hasNext()) {
			SVDBItem it = i_it.nextItem();
			
			switch (it.getType()) {
				case VarDecl: {
					SVDBVarDeclItem v = (SVDBVarDeclItem)it;
					assertNotNull("TypeInfo for variable " + 
							v.getParent().getName() + "." + v.getName() + " is null",
							v.getTypeInfo());
				}
				break;
			}
		}
		
	}

}

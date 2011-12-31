package net.sf.sveditor.core.db.refs;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;

public abstract class AbstractSVDBFileRefFinder {
	private SVDBFile			fFile;
	
	public void visitFile(SVDBFile file) {
		fFile = file;
		visit((ISVDBItemBase)file);
		visitChildParent(fFile);
	}
	
	protected void visitChildParent(ISVDBChildParent parent) {
		for (ISVDBChildItem c : parent.getChildren()) {
			visitChild(c);
		}
	}
	
	protected void visitChild(ISVDBChildItem c) {
		switch (c.getType()) {
			// Nothing to do at this level. 
			case ModuleDecl:
			case InterfaceDecl:
			case ProgramDecl:
			case Task:
			case Function:
				break;
		
			// Class may have a super-class, in addition
			// to body items
			case ClassDecl:
				break;
				
				
		}
	}
	
	protected abstract void visit(ISVDBItemBase item);

}

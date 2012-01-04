package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public abstract class AbstractSVDBFileRefFinder {
	private SVDBFile					fFile;
	private Stack<ISVDBChildItem>		fScopeStack;
	
	protected enum RefType {
		TypeReference,
		FieldReference
	}
	
	public void visitFile(SVDBFile file) {
		fFile = file;
		fScopeStack.push(fFile);
		visitChildParent(fFile);
		fScopeStack.pop();
	}
	
	protected void visitChildParent(ISVDBChildParent parent) {
		for (ISVDBChildItem c : parent.getChildren()) {
			visitChild(c);
		}
	}
	
	protected void visitChild(ISVDBChildItem c) {
		fScopeStack.push(c);
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
			case ClassDecl: {
				SVDBClassDecl cls = (SVDBClassDecl)c;
				if (cls.getSuperClass() != null) {
					SVDBTypeInfoClassType cls_t = cls.getSuperClass();
					visitRef(null, RefType.TypeReference, cls_t.getName());
				}
				} break;
				
			case VarDeclStmt: {
				SVDBVarDeclStmt var_decl = (SVDBVarDeclStmt)c;
				if (var_decl.getTypeInfo().getType() == SVDBItemType.TypeInfoUserDef) {
					SVDBTypeInfoUserDef ut = (SVDBTypeInfoUserDef)var_decl.getTypeInfo();
					visitRef(null, RefType.TypeReference, ut.getName());
				}
				} break;
		}
		
		if (c instanceof ISVDBChildParent) {
			visitChildParent((ISVDBChildParent)c);
		}
		fScopeStack.pop();
	}
	
	protected void visitRef(SVDBLocation loc, RefType type, String name) {
		System.out.println("reference: " + type + " : " + name);
	}

}

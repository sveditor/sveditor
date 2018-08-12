package net.sf.sveditor.core.db.symtab;

import java.util.Stack;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBSymTab;
import net.sf.sveditor.core.db.SVDBTFParamList;
import net.sf.sveditor.core.db.SVDBVisitorBase;
import net.sf.sveditor.core.db.index.ISVDBDeclCacheFileAttr;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVSymbolTableBuilder extends SVDBVisitorBase implements ISVDBDeclCacheFileAttr {
	private ISVDBIndex						fIndex;
	private boolean							fDebugEn;
	private LogHandle						fLog;
	private Stack<SVSymTabLevelBuilder>		fLevelStack;
	private int								fScopeIndex;
//	private Stack<E>
	
	public SVSymbolTableBuilder(ISVDBIndex index) {
		fIndex = index;
		fLog = LogFactory.getLogHandle("SVSymbolTableBuilder");
		fLog.addLogLevelListener((ILogHandle h) -> fDebugEn = h.getDebugLevel() > 0);
		fDebugEn = fLog.getDebugLevel() > 0;
		fLevelStack = new Stack<>();
	}

	public void build() {
		Iterable<String> paths = fIndex.getFileList(new NullProgressMonitor(), 
				FILE_ATTR_ROOT_FILE+FILE_ATTR_SRC_FILE+FILE_ATTR_SV_FILE);
	
		for (String path : paths) {
			System.out.println("Path: " + path);
			SVDBFile file = fIndex.findFile(path);
			
			// build the symbol table for this root file
			file.accept(this);
		}
	}
	
	@Override
	public void visit_file(SVDBFile f) {
		// Clear out stack
		fLevelStack.push(new SVSymTabLevelBuilder(f));
		if (fDebugEn) {
			fLog.debug("--> visit_file");
		}
		super.visit_file(f);
		
		// TODO: 
		
		if (fDebugEn) {
			fLog.debug("<-- visit_file");
		}
	}
	
	@Override
	public void visit_function_decl(SVDBFunction f) {
		if (fDebugEn) {
			fLog.debug("--> visit_function_decl");
		}
		SVSymTabLevelBuilder level = fLevelStack.peek();
		// Add ourselves to the enclosing scope
		level.add(f, fScopeIndex);
		
		
		// Add a level for the parameters
		fLevelStack.push(new SVSymTabLevelBuilder(f.getParams()));
		
		// Add a level for function body
		fLevelStack.push(new SVSymTabLevelBuilder(f));
		
		super.visit_scope(f);
		
		// Pop the function body level
		// TODO: create the symbol table
		level = fLevelStack.pop();
		
		// Pop the parameter-list level
		// TODO: create the symbol table
		level = fLevelStack.pop();
		
		if (fDebugEn) {
			fLog.debug("<-- visit_function_decl");
		}
	}

	@Override
	public void visit_package_decl(SVDBPackageDecl p) {
		if (fDebugEn) {
			fLog.debug("--> visit_package_decl");
		}
		fLevelStack.push(new SVSymTabLevelBuilder(p));
		
		// TODO Auto-generated method stub
		super.visit_package_decl(p);
		
		SVSymTabLevelBuilder level = fLevelStack.pop();
		SVDBSymTab tab = level.build();
		for (int i=0; i<tab.getRefs().length; i++) {
			String name = tab.getNames()[i];
			int ref = tab.getRefs()[i];
			ISVDBChildItem item = tab.get(p, i);
			System.out.println("Symbol: " + name + " " + item + " " + 
					SVDBSymTab.getIndex(ref) + " " +
					SVDBSymTab.getSubindex(ref));
		}
		if (fDebugEn) {
			fLog.debug("<-- visit_package_decl");
		}
	}
	
	@Override
	protected void visit_scope(ISVDBChildParent p) {
		int scope_index_save = fScopeIndex;
		try {
			fScopeIndex = 0;
			for (ISVDBChildItem c : p.getChildren()) {
				c.accept(this);
				fScopeIndex++;
			}
		} finally {
			fScopeIndex = scope_index_save;
		}
	}
	
	@Override
	public void visit_tf_param_list(SVDBTFParamList p) {
		// The caller will have already setup the level for us
		SVSymTabLevelBuilder level = fLevelStack.peek();
	
		int index=0;
		for (SVDBParamPortDecl param : p.getParams()) {
			int subindex=0;
			for (SVDBVarDeclItem v : param.getVarList()) {
				if (!level.add(v, index, subindex)) {
					// TODO: 
				}
				subindex++;
			}

			index++;
		}
	}
	
	@Override
	public void visit_var_decl_stmt(SVDBVarDeclStmt s) {
		SVSymTabLevelBuilder level = fLevelStack.peek();
		
		if (fDebugEn) {
			fLog.debug("--> visit_var_decl_stmt");
		}
		
		ISVDBChildParent p = (ISVDBChildParent)s.getParent();
		int index = 0;
		for (ISVDBChildItem c : p.getChildren()) {
			if (c == s) {
				break;
			} else {
				index++;
			}
		}
		
		fLog.debug("  index=" + index);
	
		int subindex = 0;
		for (SVDBVarDeclItem v : s.getVarList()) {
			fLog.debug("Variable: " + v.getName());
			if (!level.add(v, index, subindex)) {
				System.out.println("NOTE: duplicate symbol: " + v.getName());
				// TODO: duplicate symbol
			}
			subindex++;
		}
		// TODO Auto-generated method stub
		super.visit_var_decl_stmt(s);
		
		if (fDebugEn) {
			fLog.debug("<-- visit_var_decl_stmt");
		}
	}
}

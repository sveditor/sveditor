package net.sf.sveditor.vhdl.core.parser;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.vhdl.VHEntityDecl;
import antlr.Token;
import parser.Module;
import parser.ModuleInstance;

public class Tracker extends parser.Tracker {
	private Stack<ISVDBAddChildItem>			fActiveScope;
	
	public Tracker() {
		fActiveScope = new Stack<ISVDBAddChildItem>();
		fActiveScope.push(new SVDBFile());
	}

	public void addInstance(Token ref, Token m) {
		
	}
	
	public void addModule(Token m) {
		
	}
	
	public void beginEntityDecl(Token id) {
		VHEntityDecl entity = new VHEntityDecl(id.getText());
		fActiveScope.push(entity);
	}
	
	public void endEntityDecl() {
		fActiveScope.pop();
	}
}

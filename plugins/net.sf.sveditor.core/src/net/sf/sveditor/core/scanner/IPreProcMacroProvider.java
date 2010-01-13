package net.sf.sveditor.core.scanner;

import net.sf.sveditor.core.db.SVDBMacroDef;

public interface IPreProcMacroProvider {
	
	SVDBMacroDef findMacro(String name, int lineno);
	
	void addMacro(SVDBMacroDef macro);
	
	void setMacro(String key, String value);

}

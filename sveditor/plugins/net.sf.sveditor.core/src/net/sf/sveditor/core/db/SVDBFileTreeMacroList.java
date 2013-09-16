package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBFileTreeMacroList extends SVDBItemBase {
	public List<SVDBMacroDef>			fMacroList;
	
	public SVDBFileTreeMacroList() {
		super(SVDBItemType.FileTreeMacroList);
		fMacroList = new ArrayList<SVDBMacroDef>();
	}
	
	public List<SVDBMacroDef> getMacroList() {
		return fMacroList;
	}
	
	public void addMacro(SVDBMacroDef m) {
		for (int i=0; i<fMacroList.size(); i++) {
			if (fMacroList.get(i).getName().equals(m.getName())) {
				fMacroList.remove(i);
				break;
			}
		}
		fMacroList.add(m);
	}

}

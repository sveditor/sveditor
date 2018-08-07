package net.sf.sveditor.core.db;

import java.util.List;
import java.util.Map;

/**
 * SVDBSymTab stores declaration names and references to the 
 * declaration elements within the declaring scope.
 * 
 * In other words, the object for fNames[i] can be found
 * in scope.getChildItem(fRefs[i])
 * 
 * @author ballance
 *
 */
public class SVDBSymTab {
	
	public String				fNames[];
	public Integer				fRefs[];
	
	public SVDBSymTab() { }
	
	public SVDBSymTab(Map<String, Integer> symtab) { 
	}
	
	public String [] getNames() {
		return fNames;
	}
	
	public void setNames(List<String> names) {
		fNames = names.toArray(new String[names.size()]);
	}
	
	public Integer [] getRefs() {
		return fRefs;
	}
	
	public void setRefs(List<Integer> refs) {
		fRefs = refs.toArray(new Integer[refs.size()]);
	}

}

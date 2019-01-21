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
	
	public static int mkRef(int index, int subindex) {
		return (index << 10) | (subindex & 0x3FF);
	}
	
	public static int getIndex(int ref) {
		return (ref >> 10);
	}
	
	public static int getSubindex(int ref) {
		int subindex = (ref & 0x3FF);
		if ((subindex & 0x200) != 0) {
			subindex = -1;
		}
		return subindex;
	}
	
	public SVDBSymTab() { }
	
	public SVDBSymTab(
			String			names[],
			Integer			refs[]) {
		fNames = names;
		fRefs = refs;
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

	public ISVDBChildItem get(ISVDBChildParent p, int idx) {
		ISVDBChildItem ret = null;
		int index = getIndex(fRefs[idx]);
		int subindex = getSubindex(fRefs[idx]);
	
		for (ISVDBChildItem c : p.getChildren()) {
			if (index == 0) {
				ret = c;
				break;
			}
			index--;
		}
		
		if (subindex != -1) {
			for (ISVDBChildItem c : ((ISVDBChildParent)ret).getChildren()) {
				if (subindex == 0) {
					ret = c;
					break;
				}
				subindex--;
			}
		}
	
		return ret;
	}
}

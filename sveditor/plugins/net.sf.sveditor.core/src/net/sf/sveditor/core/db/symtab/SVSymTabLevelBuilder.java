package net.sf.sveditor.core.db.symtab;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBSymTab;

/**
 * Holds information about one level of symbol table
 * 
 * @author ballance
 *
 */
public class SVSymTabLevelBuilder {
	private Map<String, Sym>		fSymTab;
	private ISVDBChildParent		fScope;
	
	public static class Sym {
		private ISVDBNamedItem	fItem;
		private int				fId;
		private int				fIndex;
		private int				fSubIndex;
		
		public Sym(
				ISVDBNamedItem 	item, 
				int				id,
				int 			index, 
				int 			subindex) {
			fItem = item;
			fId   = id;
			fIndex = index;
			fSubIndex = subindex;
		};
		
		public int index() {
			return fIndex;
		}
		
		public int subindex() {
			return fSubIndex;
		}
		
		public String name() {
			return fItem.getName();
		}
		
		public ISVDBNamedItem getItem() {
			return fItem;
		}
		
		public int id() {
			return fId;
		}
	}
	
	public SVSymTabLevelBuilder(ISVDBChildParent scope) {
		fSymTab = new HashMap<>();
		fScope = scope;
	}
	
	public SVDBSymTab build() {
		String names[] = new String[fSymTab.size()];
		Integer refs[] = new Integer[fSymTab.size()];
		
		for (Sym s : fSymTab.values()) {
			names[s.id()] = s.name();
			refs[s.id()] = SVDBSymTab.mkRef(s.index(), s.subindex());
		}
	
		return new SVDBSymTab(names, refs);
	}
	
	public boolean add(
			ISVDBNamedItem	item,
			int				index,
			int				subindex) {
		String name = item.getName();
		if (fSymTab.containsKey(name)) {
			return false;
		} else {
			Sym sym = new Sym(item, fSymTab.size(), index, subindex);
			fSymTab.put(name, sym);
			return true;
		}
	}
	
	public boolean add(ISVDBNamedItem item, int index) {
		return add(item, index, -1);
	}
	
	public Sym get(String name) {
		return fSymTab.get(name);
	}
	
	public ISVDBChildItem getItem(String name) {
		Sym sym = fSymTab.get(name);
		if (sym != null) {
			int index=0;
			ISVDBChildItem item = null;
			
			for (ISVDBChildItem c : fScope.getChildren()) {
				if (sym.index() == index) {
					item = c;
					break;
				}
				index++;
			}
			
			if (sym.subindex() != -1) {
				// Search down a level
				ISVDBChildParent p = (ISVDBChildParent)item;
			
				int subindex=0;
				for (ISVDBChildItem c : p.getChildren()) {
					if (sym.subindex() == subindex) {
						item = c;
						break;
					}
					subindex++;
				}
			}
		
			return item;
		} else {
			return null;
		}
	}
}

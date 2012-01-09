package net.sf.sveditor.core.db.refs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBLocation;

public class SVDBFileRefCollector extends AbstractSVDBFileRefFinder {
	private Map<RefType, Set<String>>	fReferences;
	
	public SVDBFileRefCollector() {
		fReferences = new HashMap<AbstractSVDBFileRefFinder.RefType, Set<String>>();
	}
	
	public Set<RefType> getRefTypeSet() {
		return fReferences.keySet();
	}
	
	public Set<String> getRefSet(RefType type) {
		return fReferences.get(type);
	}

	@Override
	protected void visitRef(SVDBLocation loc, RefType type, String name) {
		if (!fReferences.containsKey(type)) {
			fReferences.put(type, new HashSet<String>());
		}
		Set<String> set = fReferences.get(type);
		if (!set.contains(name)) {
			set.add(name);
		}
	}
}

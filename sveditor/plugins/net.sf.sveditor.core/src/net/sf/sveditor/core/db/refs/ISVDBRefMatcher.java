package net.sf.sveditor.core.db.refs;


public interface ISVDBRefMatcher {
	
	boolean matches(
			ISVDBRefSearchSpec		ref_spec,
			SVDBRefItem				item);

}

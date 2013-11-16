package net.sf.sveditor.core.db.refs;


public interface ISVDBRefVisitor {
	
	void visitRef(
			ISVDBRefSearchSpec		ref_spec,
			SVDBRefItem				item);

}

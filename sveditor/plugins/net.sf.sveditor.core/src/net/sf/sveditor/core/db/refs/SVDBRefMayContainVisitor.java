package net.sf.sveditor.core.db.refs;

public class SVDBRefMayContainVisitor implements ISVDBRefVisitor {
	private boolean					fMayContain;
	
	public boolean mayContain() {
		return fMayContain;
	}

	@Override
	public void visitRef(ISVDBRefSearchSpec ref_spec, SVDBRefItem item) {
		fMayContain = true;
	}
}

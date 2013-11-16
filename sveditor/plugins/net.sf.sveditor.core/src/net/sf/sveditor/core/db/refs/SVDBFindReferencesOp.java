package net.sf.sveditor.core.db.refs;

import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;

public class SVDBFindReferencesOp implements ISVDBIndexOperation {
	private ISVDBRefSearchSpec		fSearchSpec;
	private ISVDBRefVisitor			fVisitor;
	
	public SVDBFindReferencesOp(
			ISVDBRefSearchSpec	ref_spec,
			ISVDBRefVisitor		visitor) {
		fSearchSpec = ref_spec;
		fVisitor = visitor;
	}
	

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		index.findReferences(monitor, fSearchSpec, fVisitor);
	}

}

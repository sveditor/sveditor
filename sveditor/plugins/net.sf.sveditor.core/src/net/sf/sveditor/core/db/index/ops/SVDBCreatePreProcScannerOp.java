package net.sf.sveditor.core.db.index.ops;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexOperationRunner;
import net.sf.sveditor.core.preproc.ISVPreProcessor;

public class SVDBCreatePreProcScannerOp implements ISVDBIndexOperation {
	private String					fPath;
	private ISVPreProcessor			fPreProc;
	
	public SVDBCreatePreProcScannerOp(String path) {
		fPath = path;
		fPreProc = null;
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		ISVDBIndexInt index_int = (ISVDBIndexInt)index;
		
		fPreProc = index_int.createPreProcScanner(fPath);
	}
	
	public static ISVPreProcessor op(ISVDBIndexOperationRunner runner, String path) {
		SVDBCreatePreProcScannerOp op = new SVDBCreatePreProcScannerOp(path);
		runner.execOp(new NullProgressMonitor(), op, true);
		
		return op.fPreProc;
	}

}

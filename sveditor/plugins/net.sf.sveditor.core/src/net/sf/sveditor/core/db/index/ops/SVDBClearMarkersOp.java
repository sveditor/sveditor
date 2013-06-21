package net.sf.sveditor.core.db.index.ops;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;

public class SVDBClearMarkersOp implements ISVDBIndexOperation {

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		monitor.beginTask("Clear markers for " + index.getBaseLocation(), 10000);
		Iterable<String> paths = index.getFileList(new NullProgressMonitor());
		ISVDBFileSystemProvider fs_provider = index.getFileSystemProvider();
		
		for (String path : paths) {
			fs_provider.clearMarkers(path);
		}
		
		monitor.done();
	}

}

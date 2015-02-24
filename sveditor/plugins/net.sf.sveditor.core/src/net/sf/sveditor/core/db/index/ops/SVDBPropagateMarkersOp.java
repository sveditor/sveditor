package net.sf.sveditor.core.db.index.ops;

import java.util.List;

import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBPropagateMarkersOp implements ISVDBIndexOperation {
	private List<String>				fPreFiles;
	
	public SVDBPropagateMarkersOp() {
		this(null);
	}
	
	public SVDBPropagateMarkersOp(List<String> pre_files) {
		fPreFiles = pre_files;
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		Iterable<String> paths = index.getFileList(new NullProgressMonitor(), 
				ISVDBDeclCache.FILE_ATTR_SRC_FILE+
				ISVDBDeclCache.FILE_ATTR_ARG_FILE+
				ISVDBDeclCache.FILE_ATTR_HAS_MARKERS);
		ISVDBFileSystemProvider fs_provider = index.getFileSystemProvider();
		
		monitor.beginTask("Propagate markers for " + index.getBaseLocation(), 10000);
	
		for (String path : paths) {
			if (monitor.isCanceled()) {
				break;
			}
			
			if (fPreFiles != null) {
				fPreFiles.remove(path);
			}
			
			List<SVDBMarker> m_l = index.getMarkers(path);
			
//			List<SVDBMarker> m_l = new ArrayList<SVDBMarker>();
			fs_provider.clearMarkers(path);
			
			if (m_l != null && m_l.size() > 0) {
				monitor.subTask("Propagate markers for " + path);
				for (SVDBMarker m : m_l) {
					int lineno = -1;
					String msg = m.getMessage();
					String type = "";
					
					if (m.getLocation() != null) {
						lineno = m.getLocation().getLine();
					}
					
					switch (m.getMarkerType()) {
						case Error:
							type = ISVDBFileSystemProvider.MARKER_TYPE_ERROR;
							break;
						case Warning:
							type = ISVDBFileSystemProvider.MARKER_TYPE_WARNING;
							break;
						case Info:
							type = ISVDBFileSystemProvider.MARKER_TYPE_INFO;
							break;
						case Task:
							type = ISVDBFileSystemProvider.MARKER_TYPE_TASK;
							break;
					}
					
					fs_provider.addMarker(path, type, lineno, msg);
				}
			}
			
			monitor.worked(1);
		}
	
		// Handle any files that 'disappeared' during the index operation
		if (fPreFiles != null) {
			for (String path : fPreFiles) {
				fs_provider.clearMarkers(path);
			}
		}

		monitor.done();
	}

}

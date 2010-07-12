package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.core.db.SVDBFile;

import org.eclipse.core.runtime.IAdaptable;

public class ProjectPathsFileWrapper implements IAdaptable {
	private SVDBFile				fFile;
	
	public ProjectPathsFileWrapper(SVDBFile f) {
		fFile = f;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		if (adapter.equals(SVDBFile.class)) {
			return fFile;
		}
		return null;
	}
	
}

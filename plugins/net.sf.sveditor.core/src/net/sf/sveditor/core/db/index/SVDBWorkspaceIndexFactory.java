package net.sf.sveditor.core.db.index;

import org.eclipse.core.runtime.Path;

public class SVDBWorkspaceIndexFactory implements ISVDBIndexFactory {

	public ISVDBIndex createSVDBIndex(String base_location) {
		return new SVDBWorkspaceIndex(new Path(base_location), ISVDBIndex.IT_BuildPath);
	}

}

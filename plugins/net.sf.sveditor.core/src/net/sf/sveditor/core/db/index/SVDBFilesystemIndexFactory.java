package net.sf.sveditor.core.db.index;

import java.io.File;

public class SVDBFilesystemIndexFactory implements ISVDBIndexFactory {

	public ISVDBIndex createSVDBIndex(String base_location) {
		return new SVDBFilesystemIndex(new File(base_location), ISVDBIndex.IT_BuildPath);
	}

}

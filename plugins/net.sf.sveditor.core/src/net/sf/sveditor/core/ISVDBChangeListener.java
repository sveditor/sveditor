package net.sf.sveditor.core;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;

public interface ISVDBChangeListener {
	
	void SVDBFileChanged(
			SVDBFile 			file,
			List<SVDBItem>		adds,
			List<SVDBItem>		removes,
			List<SVDBItem>		changes);

}

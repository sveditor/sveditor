package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFileTree;

/**
 * Provides a path to a given file, listing include locations, etc
 * 
 * @author ballance
 *
 */
public class SVDBFilePath {
	
	private List<Tuple<SVDBFileTree, ISVDBItemBase>>		fFilePath;
	
	public SVDBFilePath() {
		fFilePath = new ArrayList<Tuple<SVDBFileTree,ISVDBItemBase>>();
	}
	
	public void addPath(SVDBFileTree ft, ISVDBItemBase item) {
		fFilePath.add(new Tuple<SVDBFileTree, ISVDBItemBase>(ft, item));
	}
	
	public List<Tuple<SVDBFileTree, ISVDBItemBase>> getPath() {
		return fFilePath;
	}

}

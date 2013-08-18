package net.sf.sveditor.core.preproc;

import java.io.InputStream;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFileTreeMacroList;

public interface ISVPreProcIncFileProvider {

	/**
	 * 
	 * @param incfile
	 * @return
	 */
	Tuple<String, List<SVDBFileTreeMacroList>> findCachedIncFile(String incfile);

	public void addCachedIncFile(String incfile, String rootfile);
	
	/**
	 * 
	 * @param incfile
	 * @return Tuple of <FullPath, Data> or NULL if the file
	 *  cannot be located
	 */
	Tuple<String, InputStream> findIncFile(String incfile);

}

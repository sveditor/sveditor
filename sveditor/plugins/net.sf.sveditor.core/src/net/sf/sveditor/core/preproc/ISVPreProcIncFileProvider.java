package net.sf.sveditor.core.preproc;

import java.io.InputStream;

import net.sf.sveditor.core.Tuple;

public interface ISVPreProcIncFileProvider {

	/**
	 * 
	 * @param incfile
	 * @return Tuple of <FullPath, Data> or NULL if the file
	 *  cannot be located
	 */
	Tuple<String, InputStream> findIncFile(String incfile);

}

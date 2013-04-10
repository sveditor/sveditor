package net.sf.sveditor.core.preproc;

import java.util.Map;

import net.sf.sveditor.core.Tuple;

public interface ISVPreProcIncFileCache {
	
	Tuple<String, Map<String, String>> findIncCache(
			String 					incfile, 
			Map<String, String> 	references);

	void setIncCache(
			String					incpath,
			String					fullpath,
			Map<String, String>		references);
}

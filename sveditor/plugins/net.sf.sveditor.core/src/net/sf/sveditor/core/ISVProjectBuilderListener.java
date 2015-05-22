package net.sf.sveditor.core;

import java.util.Map;

public interface ISVProjectBuilderListener {
	
	void build_start(
			int						kind,
			Map<String, String>		args);
	
	void build_complete(
			int						kind,
			Map<String, String>		args);

}

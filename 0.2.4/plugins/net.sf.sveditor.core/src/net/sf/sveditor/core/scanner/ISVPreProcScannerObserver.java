package net.sf.sveditor.core.scanner;

import java.util.List;

public interface ISVPreProcScannerObserver {
	
	void init(ISVScanner scanner);
	
	void enter_file(String filename);
	
	void leave_file();

	void preproc_define(String key, List<String> params, String value);
	
	void preproc_include(String path);
	
	void enter_preproc_conditional(String type, String conditional);
	
	void leave_preproc_conditional();
	
	void comment(String comment);

	void enter_package(String name);
	
	void leave_package();

}

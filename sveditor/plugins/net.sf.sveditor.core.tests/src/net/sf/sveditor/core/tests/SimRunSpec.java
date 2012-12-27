package net.sf.sveditor.core.tests;

import java.util.ArrayList;
import java.util.List;

public class SimRunSpec {
	private List<String>			fTopModules;
	private List<String>			fSimOpts;
	private String					fTranscriptPath;
	
	public SimRunSpec() {
		fTopModules = new ArrayList<String>();
		fSimOpts = new ArrayList<String>();
	}
	
	public void addTopModule(String top) {
		fTopModules.add(top);
	}
	
	public List<String> getTopModules() {
		return fTopModules;
	}
	
	public void addSimOptions(String opt) {
		fSimOpts.add(opt);
	}
	
	public List<String> getSimOptions() {
		return fSimOpts;
	}
	
	public String getTranscriptPath() {
		return fTranscriptPath;
	}

	public void setTranscriptPath(String path) {
		fTranscriptPath = path;
	}

}

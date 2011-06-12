package net.sf.sveditor.core.job_mgr;

public interface ISVEditorJobListener {
	
	void jobStarted(ISVEditorJob job);
	
	void jobEnded(ISVEditorJob job);

}

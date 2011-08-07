package net.sf.sveditor.core.job_mgr;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVEditorJob {
	
	String getName();
	
	/**
	 * Returns the 'kind' of job. This controls which queue the job is placed in
	 * 
	 * @return
	 */
	String getKind();
	
	void pre_run();
	
	void run(IProgressMonitor monitor) throws SVJobException;
	
	void post_run();
	
	void addListener(ISVEditorJobListener l);
	
	void removeListener(ISVEditorJobListener l);
	
}

package net.sf.sveditor.core.preproc;

public interface ISVPreProcOutputFileChangeListener {
	
	void fileChanged(
			int			old_id,
			int			new_id);

}

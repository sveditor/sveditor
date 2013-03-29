package net.sf.sveditor.core.db.index;

import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexChangePlanner {
	
	ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes);
	
	void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan);

}

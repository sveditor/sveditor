package net.sf.sveditor.core.db.index.builder;

import java.util.List;

import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexChangePlanner {
	
	void setIndexBuilder(ISVDBIndexBuilder builder);
	
	ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes);
	
	void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan);

}

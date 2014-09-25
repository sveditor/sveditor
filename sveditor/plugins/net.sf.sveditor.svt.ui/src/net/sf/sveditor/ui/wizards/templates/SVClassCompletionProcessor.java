package net.sf.sveditor.ui.wizards.templates;

import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

public class SVClassCompletionProcessor extends AbstractCompletionProcessor {
	private ISVDBIndexIterator				fIndexIterator;
	
	public SVClassCompletionProcessor(ISVDBIndexIterator index_it) {
		fIndexIterator = index_it;
		fLog = LogFactory.getLogHandle("SVClassCompletionProcessor");
	} 

	@Override
	protected ISVDBIndexIterator getIndexIterator() {
		return fIndexIterator;
	}

	@Override
	protected SVDBFile getSVDBFile() {
		return new SVDBFile("");
	}

	@Override
	protected ISVStringPreProcessor getPreProcessor(int limit_lineno) {
		return null;
	}

}

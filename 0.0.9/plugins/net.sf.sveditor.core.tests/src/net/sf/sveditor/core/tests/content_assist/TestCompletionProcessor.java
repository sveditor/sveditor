package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;

public class TestCompletionProcessor extends AbstractCompletionProcessor {
	
	private SVDBFile					fSVDBFile;
	private ISVDBIndexIterator			fIndexIterator;
	
	public TestCompletionProcessor(SVDBFile file, ISVDBIndexIterator iterator) {
		fSVDBFile      = file;
		fIndexIterator = iterator;
		fLog = LogFactory.getDefault().getLogHandle("TestCompletionProcessor");
	}

	@Override
	protected ISVDBIndexIterator getIndexIterator() {
		return fIndexIterator;
	}

	@Override
	protected SVDBFile getSVDBFile() {
		return fSVDBFile;
	}

}

package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class TestCompletionProcessor extends AbstractCompletionProcessor {
	
	private SVDBFile					fSVDBFile;
	private ISVDBIndexIterator			fIndexIterator;
	
	public TestCompletionProcessor(SVDBFile file, ISVDBIndexIterator iterator) {
		fSVDBFile      = file;
		fIndexIterator = iterator;
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

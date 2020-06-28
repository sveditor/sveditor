/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

public class TestCompletionProcessor extends AbstractCompletionProcessor {
	
	private SVDBFile					fSVDBFile;
	private ISVDBIndexIterator			fIndexIterator;
	private ISVStringPreProcessor		fPreProcessor;
	//private boolean						fEnableKeywords;
	
	public TestCompletionProcessor(LogHandle log, SVDBFile file, ISVDBIndexIterator iterator) {
		fSVDBFile      = file;
		fIndexIterator = iterator;
		fLog = LogFactory.getLogHandle(log.getName() + ".TestCompletionProcessor");
	}

	public TestCompletionProcessor(String name, SVDBFile file, ISVDBIndexIterator iterator) {
		fSVDBFile      = file;
		fIndexIterator = iterator;
		fLog = LogFactory.getLogHandle(name + ".TestCompletionProcessor");
	}

	public TestCompletionProcessor(SVDBFile file, ISVDBIndexIterator iterator) {
		fSVDBFile      = file;
		fIndexIterator = iterator;
		fLog = LogFactory.getLogHandle("TestCompletionProcessor");
	}
	
	@Override
	protected ISVDBIndexIterator getIndexIterator() {
		return fIndexIterator;
	}

	@Override
	protected SVDBFile getSVDBFile() {
		return fSVDBFile;
	}

	@Override
	protected ISVStringPreProcessor getPreProcessor(int limit_lineno) {
		return fPreProcessor;
	}

	public void setPreProcessor(ISVStringPreProcessor preproc) {
		fPreProcessor = preproc;
	}

}

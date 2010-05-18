/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;

public class TestCompletionProcessor extends AbstractCompletionProcessor {
	
	private SVDBFile					fSVDBFile;
	private ISVDBIndexIterator			fIndexIterator;
	
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

}

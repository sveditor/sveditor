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


package org.sveditor.ui.tests.editor;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.tests.FileIndexIterator;
import org.sveditor.ui.editor.ISVEditor;
import org.sveditor.ui.tests.UiReleaseTests;
import org.sveditor.ui.tests.utils.editor.AutoEditTester;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.StringInputStream;
import org.sveditor.core.db.ISVDBFileFactory;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;

public class SVEditorTester implements ISVEditor {
	private IDocument				fDoc;
	private AutoEditTester			fAutoEditTester;
	private ISVDBIndexIterator		fIndexIt;
	private SVDBFile				fSVDBFile;
	private ITextSelection			fTextSel;
	
	public SVEditorTester(
			AutoEditTester			auto_ed,
			ISVDBIndexIterator		index_it,
			SVDBFile				file) {
		fAutoEditTester = auto_ed;
		fIndexIt 		= index_it;
		fSVDBFile 		= file;
		fTextSel    	= null;
	}

	public SVEditorTester(String doc, String filename, ISVDBIndexCacheMgr cache_mgr) throws BadLocationException {
		fAutoEditTester = UiReleaseTests.createAutoEditTester();
		fAutoEditTester.setContent(doc);

		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		fSVDBFile = factory.parse(new StringInputStream(doc), filename, markers);

		ISVDBIndexCache cache = FileIndexIterator.createCache(cache_mgr);
		fIndexIt = new FileIndexIterator(fSVDBFile, cache);
	}

	public IDocument getDocument() {
		if (fAutoEditTester != null) {
			return fAutoEditTester.getDocument();
		} else {
			return fDoc;
		}
	}
	
	public AutoEditTester getAutoEdit() {
		return fAutoEditTester;
	}
	
	public void setSelection(ITextSelection sel) {
		fTextSel = sel;
	}

	public ISVDBIndexIterator getIndexIterator() {
		return fIndexIt;
	}

	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}

	public ITextSelection getTextSel() {
		return fTextSel;
	}

}

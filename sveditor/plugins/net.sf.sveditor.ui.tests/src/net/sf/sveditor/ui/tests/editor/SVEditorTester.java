/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.tests.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.ui.editor.ISVEditor;
import net.sf.sveditor.ui.tests.UiReleaseTests;
import net.sf.sveditor.ui.tests.utils.editor.AutoEditTester;

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

	public SVEditorTester(
			SVCoreTestCaseBase		test,
			String 					doc) throws BadLocationException {
		fAutoEditTester = UiReleaseTests.createAutoEditTester();
		fAutoEditTester.setContent(doc);
		
		SVDBIndexRegistry rgy = test.getIndexRgy();
		File tmpdir = test.getTmpDir();
		
		TestUtils.copy(
				new File(tmpdir, test.getName() + ".sv").getAbsolutePath(),
				new File(tmpdir, test.getName() + ".f"));
		TestUtils.copy(
				doc,
				new File(tmpdir, test.getName() + ".sv").getAbsoluteFile());
			
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), 
				"global", 
				new File(tmpdir, test.getName() + ".f").getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE,
				null);
		
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));

//		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
//		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
//		fSVDBFile = factory.parse(new StringInputStream(doc), filename, markers);
//
//		ISVDBIndexCache cache = FileIndexIterator.createCache(cache_mgr);
//		fIndexIt = new FileIndexIterator(fSVDBFile, cache);
		fIndexIt = index;
		TestCase.assertNotNull(index);
		fSVDBFile = index.findFile(
				new File(tmpdir, test.getName() + ".sv").getAbsolutePath());
		TestCase.assertNotNull(fSVDBFile);
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

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


package net.sf.sveditor.ui.tests.editor;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBFileOverrideIndex;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.BadLocationException;

public class TestIndexAssociation extends SVEditorTestCaseBase {

	public void disabled_testBuiltinAvailableInShadow_WS() throws CoreException, InterruptedException, BadLocationException {
		SVCorePlugin.getDefault().enableDebug(false);

		CoreReleaseTests.clearErrors();

		IProject p = TestUtils.createProject(getName());
		
		// Create simple class file
		String class_file =
				"class cls1;\n" +
				"	extern function void f1();\n" +
				"endclass\n" +
				"\n" +
				"\n" +
				"\n" +
				"function void cls1::f1;\n" +
				"endfunction\n" +
				"\n"
				;
		
		TestUtils.copy(class_file, p.getFile("cls1.svh"));
		
		SVEditor editor = openEditor("${workspace_loc}/" + getName() + "/cls1.svh");
		
		ISVDBIndex index = editor.getSVDBIndex();
		assertTrue(index instanceof SVDBFileOverrideIndex);
		SVDBFileOverrideIndex index_w = (SVDBFileOverrideIndex)index;
		index = index_w.getBaseIndex();
	
		// Ensure that we're using a shadow index
//		assertTrue(index instanceof SVDBShadowIndex);
		
		ISVDBIndexIterator index_it = editor.getIndexIterator();
		List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"string", new SVDBFindByNameMatcher());
		
		assertEquals(1, result.size());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	public void disabled_testBuiltinAvailableInShadow_FS() throws CoreException, InterruptedException, BadLocationException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		File dir = new File(fTmpDir, "dir");
		assertTrue(dir.mkdirs());

		CoreReleaseTests.clearErrors();

		// Create simple class file
		String class_file =
				"class cls1;\n" +
				"	extern function void f1();\n" +
				"endclass\n" +
				"\n" +
				"\n" +
				"\n" +
				"function void cls1::f1;\n" +
				"endfunction\n" +
				"\n"
				;
	
		File cls1_svh = new File(dir, "cls1.svh");
		TestUtils.copy(class_file, cls1_svh);
		
		SVEditor editor = openEditor(cls1_svh.getAbsolutePath());
		
		ISVDBIndex index = editor.getSVDBIndex();
		assertTrue(index instanceof SVDBFileOverrideIndex);
		SVDBFileOverrideIndex index_w = (SVDBFileOverrideIndex)index;
		index = index_w.getBaseIndex();
	
		// Ensure that we're using a shadow index
//		assertTrue(index instanceof SVDBShadowIndex);
		
		ISVDBIndexIterator index_it = editor.getIndexIterator();
		List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"string", new SVDBFindByNameMatcher());
		
		assertEquals(1, result.size());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
}

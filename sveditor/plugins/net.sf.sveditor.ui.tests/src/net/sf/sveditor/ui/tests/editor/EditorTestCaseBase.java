package net.sf.sveditor.ui.tests.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.editor.SVAutoIndentStrategy;
import net.sf.sveditor.ui.editor.SVDocumentPartitions;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.editor.outline.SVOutlinePage;
import net.sf.sveditor.ui.tests.editor.utils.AutoEditTester;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class EditorTestCaseBase extends TestCase {
	protected LogHandle				fLog;
	protected List<IProject>			fProjects;
	protected List<ITextEditor>		fEditors;
	protected File						fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		
		fLog = LogFactory.getLogHandle(getName());
		
		cleanupWorkspace();
		
		fProjects = new ArrayList<IProject>();
		fEditors = new ArrayList<ITextEditor>();
		
		fTmpDir = TestUtils.createTempDir();
		File db = new File(fTmpDir, "db");
		
		assertTrue(db.mkdirs());
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(new TestIndexCacheFactory(db));

	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		for (ITextEditor t : fEditors) {
			t.close(false);
		}

		// Wait for the editors to close
		while (Display.getDefault().readAndDispatch()) {}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
	
		SVCorePlugin.getJobMgr().dispose();
		
		for (IProject p : fProjects) {
			TestUtils.deleteProject(p);
		}
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
		
		cleanupWorkspace();
	}
	
	protected void addProject(IProject p) {
		fProjects.add(p);
	}
	
	protected void addEditor(ITextEditor editor) {
		fEditors.add(editor);
	}

	protected SVEditor findEditor(String path) {
		SVEditor ret = null;
		
		IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		for (IWorkbenchPage p : w.getPages()) {
			for (IEditorReference ed : p.getEditorReferences()) {
				if (ed.getName().endsWith(path)) {
					IEditorPart ed_p = ed.getEditor(true);
					if (ed_p instanceof SVEditor) {
						ret = (SVEditor)ed_p;
						break;
					}
				}
			}
		}
		return ret;
	}
	
	private void cleanupWorkspace() throws CoreException {
		IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		for (IWorkbenchPage p : w.getPages()) {
			p.closeAllEditors(true);
		}
		
		// TODO: close all open projects
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		for (IProject p : root.getProjects()) {
			p.delete(true, new NullProgressMonitor());
		}
	}
	
	protected SVEditor openEditor(String path) throws PartInitException {
		IEditorPart ed = SVEditorUtil.openEditor(path);
		assertNotNull(ed);
		assertTrue((ed instanceof SVEditor));
		
		while (Display.getDefault().readAndDispatch()) {}
	
		SVEditor sv_ed = (SVEditor)ed;
		if (!fEditors.contains(sv_ed)) {
			fEditors.add(sv_ed);
		}
		
		return sv_ed;
	}

	protected Tuple<SVEditor, AutoEditTester> openAutoEditTester(String path) throws PartInitException {
		IEditorPart ed = SVEditorUtil.openEditor(path);
		assertNotNull(ed);
		assertTrue((ed instanceof SVEditor));
		
		while (Display.getDefault().readAndDispatch()) {}
	
		SVEditor sv_ed = (SVEditor)ed;
		if (!fEditors.contains(sv_ed)) {
			fEditors.add(sv_ed);
		}
		
		AutoEditTester auto_edit = new AutoEditTester(
				sv_ed.getDocument(), 
				SVDocumentPartitions.SV_PARTITIONING);
		
		auto_edit.setAutoEditStrategy(
				IDocument.DEFAULT_CONTENT_TYPE, 
				new SVAutoIndentStrategy(null, SVDocumentPartitions.SV_PARTITIONING));
		
		return new Tuple<SVEditor, AutoEditTester>(sv_ed, auto_edit);
	}
	
	protected SVOutlinePage getOutlineView(IEditorPart editor) throws PartInitException {
		IViewPart outline_v = editor.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		
		while (Display.getDefault().readAndDispatch()) {}
		
		Object ret = editor.getAdapter(IContentOutlinePage.class);
		
		assertTrue(ret instanceof SVOutlinePage);
		
		return (SVOutlinePage)ret;
	}
}

package net.sf.sveditor.ui.tests.editor;

import java.io.File;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.editor.actions.OpenDeclarationAction;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

public class TestUserLevelOperations extends TestCase {
	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
		}
	}

	public void testOpenClassDeclaration() throws CoreException, InterruptedException {
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();

		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		// Create a new project for the 
		File test_dir = new File(fTmpDir, "testArgFileIndex");
		File db_dir = new File(fTmpDir, "db");
		if (test_dir.exists()) {
			assertTrue(test_dir.delete());
		}
		assertTrue(test_dir.mkdirs());
		
		if (db_dir.exists()) {
			assertTrue(db_dir.delete());
		}
		assertTrue(db_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		IProject project_dir = TestUtils.createProject("xbus", xbus);
		
		// Setup appropriate project settings
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Add an argument-file path for the XBus example
		SVProjectFileWrapper p_wrapper = p_data.getProjectFileWrapper().duplicate();
		p_wrapper.getArgFilePaths().add(new SVDBPath("${workspace_loc}/xbus/examples/compile_questa_sv.f"));
		p_data.setProjectFileWrapper(p_wrapper);
		
		// Now, open xbus/examples/xbus_demo_tb.sv
		SVDBIndexCollectionMgr project_index = p_data.getProjectIndexMgr();
		// force index loading
		ISVDBItemIterator<SVDBItem> it = project_index.getItemIterator();
		it.nextItem();

		IEditorPart xbus_demo_tb = SVEditorUtil.openEditor("${workspace_loc}/xbus/examples/xbus_demo_tb.sv");
		assertNotNull(xbus_demo_tb);
		assertTrue((xbus_demo_tb instanceof SVEditor));
		SVEditor sveditor = (SVEditor)xbus_demo_tb;
		

		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		OpenDeclarationAction od_action = (OpenDeclarationAction)
			sveditor.getAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction");
		
		IDocument doc = sveditor.getDocument();
		int idx = doc.get().indexOf("ovm_env");
		sveditor.getSelectionProvider().setSelection(new TextSelection(idx, "ovm_env".length()));
		//sveditor.setSelection(idx, idx+"ovm_env".length(), true);

		ISVDBIndexIterator index_it = sveditor.getIndexIterator();
		System.out.println("--> Dump index");
		ISVDBItemIterator<SVDBItem> item_it = index_it.getItemIterator();
		while (item_it.hasNext()) {
			SVDBItem it_t = item_it.nextItem();
			// System.out.println("    it_t=" + it_t.getName());
		}
		System.out.println("<-- Dump index");

		while (Display.getDefault().readAndDispatch()) {}
		
		// sveditor.getSelectionProvider().getSelection()
		
		od_action.run();

		while (Display.getDefault().readAndDispatch()) {}

		// Now, need to validate
		SVEditor ovm_env = findEditor("ovm_env.svh");
		assertNotNull(ovm_env);
		
		// Now, confirm no errors
		SVDBFile ovm_env_f = ovm_env.getSVDBFile();
		SVDBTestUtils.assertNoErrWarn(ovm_env_f);
		SVDBTestUtils.assertFileHasElements(ovm_env_f, "ovm_env");
		
		
		
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
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
	
	private SVEditor findEditor(String path) {
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
}

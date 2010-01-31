package net.sf.sveditor.ui.editor.actions;

import java.io.File;
import java.net.URI;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.plugin_lib.PluginFileStore;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBOpenDeclarationIncludeNameMatcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.PluginPathEditorInput;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.IFileSystem;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorRegistry;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.FileStoreEditorInput;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenDeclarationAction extends TextEditorAction {
	private SVEditor				fEditor;
	private LogHandle				fLog;
	private boolean					fDebugEn = true;

	public OpenDeclarationAction(
			ResourceBundle			bundle,
			String					prefix,
			SVEditor				editor) {
		super(bundle, prefix, editor);
		fLog = LogFactory.getDefault().getLogHandle("OpenDeclarationAction");
		fEditor = editor;
		update();
	}

	private ITextSelection getTextSel() {
		ITextSelection sel = null;
		
		if (getTextEditor() != null) {
			ISelection sel_o = 
				getTextEditor().getSelectionProvider().getSelection();
			if (sel_o != null && sel_o instanceof ITextSelection) {
				sel = (ITextSelection)sel_o;
			} 
		}
		
		return sel;
	}

	@Override
	public void run() {
		super.run();
		
		debug("OpenDeclarationAction.run()");
		
		IDocument doc = fEditor.getDocumentProvider().getDocument(
				fEditor.getEditorInput());
		ITextSelection sel = getTextSel();
		
		int offset = sel.getOffset() + sel.getLength();
		SVDBFile    		inc_file = null;
		SVDBItem			it = null;

		SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, offset);
		SVExpressionUtils		expr_utils = new SVExpressionUtils(new SVDBFindDefaultNameMatcher());
		
		SVExprContext expr_ctxt = expr_utils.extractExprContext(scanner, true);
		
		fLog.debug("Expression Context: root=" + expr_ctxt.fRoot +
				" trigger=" + expr_ctxt.fTrigger + " leaf=" + expr_ctxt.fLeaf);

		ISVDBIndexIterator index_it = fEditor.getIndexIterator();
		
		
		// Now, iterate through the items in the file and find something
		// with the same name
		SVDBFile file = fEditor.getSVDBFile();
		
		SVDBScopeItem active_scope = SVDBSearchUtils.findActiveScope(
				file, getTextSel().getStartLine());
		
		// If this is an include lookup, then use a different matching strategy
		if (expr_ctxt.fTrigger != null && expr_ctxt.fRoot != null &&
				expr_ctxt.fTrigger.equals("`") && expr_ctxt.fRoot.equals("include")) {
			expr_utils.setMatcher(new SVDBOpenDeclarationIncludeNameMatcher());
		}

		List<SVDBItem> items = expr_utils.findItems(index_it, active_scope, expr_ctxt, false);
		
		if (items.size() > 0) {
			it = items.get(0);
		}

		if (it != null) {
			IEditorPart ed_f = openEditor(it, fEditor.getIndexIterator());
			((SVEditor)ed_f).setSelection(it, true);
		} else if (inc_file != null) {
			openEditor(inc_file.getFilePath(), fEditor.getIndexIterator());
		}
	}
	
	private IEditorPart openEditor(
			SVDBItem 			it,
			ISVDBIndexIterator	index_it) {
		SVDBItem p = it;
		// Find the file that this item belongs to
		
		while (p != null && p.getType() != SVDBItemType.File) {
			p = p.getParent();
		}
		
		String file = ((SVDBFile)p).getFilePath();
		
		return openEditor(file, index_it);
	}
	
	private IEditorPart openEditor(
			String 					file,
			ISVDBIndexIterator		index_it) {
		IFile f = null;
		String name = "";
		IEditorPart ret = null;
		
		System.out.println("openEditor: " + file);
		
		if (file != null) {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

			if (file.startsWith("${workspace_loc}")) {
				file = file.substring("${workspace_loc}".length());
				f = root.getFile(new Path(file));
				
				if (f != null) {
					name = f.getFullPath().toOSString();
				}
			} else {
				f = root.getFileForLocation(new Path(file));
				if (f != null) {
					name = f.getLocation().toString();
				} else {
					name = file;
				}
			}
			
			IWorkbench wb = PlatformUI.getWorkbench();
			IWorkbenchWindow w = wb.getActiveWorkbenchWindow();

			for (IWorkbenchPage page : w.getPages()) {
				for (IEditorReference ed_r : page.getEditorReferences()) {
					String id = ed_r.getId();

					if (!id.equals(SVUiPlugin.PLUGIN_ID + ".editor")) {
						continue;
					}
					IEditorInput in = null;

					try {
						in = ed_r.getEditorInput();
					} catch (PartInitException e) {
						e.printStackTrace();
					}

					if (in instanceof IURIEditorInput) {
						IURIEditorInput in_uri = (IURIEditorInput)in;

						debug("URI path: " + in_uri.getURI().getPath());
						
						if (in_uri.getURI().getPath().equals(name)) {
							ret = ed_r.getEditor(true);
							break;
						}
					}
				}

				if (ret != null) {
					break;
				}
			}
		}
		
		if (ret == null) {
			IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			IEditorRegistry rgy = PlatformUI.getWorkbench().getEditorRegistry();

			String leaf_name = new File(file).getName();
			IEditorDescriptor desc = rgy.getDefaultEditor(leaf_name);
			IEditorInput ed_in = null;
			
			debug("file=" + file);
			
			try {
				if (f != null) {
					ed_in = new FileEditorInput(f);
				} else if (file.startsWith("plugin:/")) {
					debug("plugin: " + file);
					IFileSystem fs = null;
					IFileStore store = null;
					try {
						fs = EFS.getFileSystem("plugin");
						store = fs.getStore(new URI(file));
					} catch (Exception e) {
						e.printStackTrace();
					}

					try {
						ed_in = new PluginPathEditorInput((PluginFileStore)store);
					} catch (CoreException e) {
						e.printStackTrace();
					}
				} else {
					File file_path = new File(file);
					IFileStore fs = EFS.getLocalFileSystem().getStore(file_path.toURI());
					ed_in = new FileStoreEditorInput(fs);
					
					// TODO: need to connect up index to filesystem
				}
				ret = w.getActivePage().openEditor(ed_in, desc.getId());

			} catch (PartInitException e) {
				e.printStackTrace();
			}
		} else {
			IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			w.getActivePage().activate(ret);
		}
		
		return ret;
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}
}

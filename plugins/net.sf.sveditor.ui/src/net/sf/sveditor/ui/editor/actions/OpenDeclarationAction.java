package net.sf.sveditor.ui.editor.actions;

import java.io.File;
import java.net.URI;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.plugin_lib.PluginFileStore;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameInClassHierarchy;
import net.sf.sveditor.core.db.search.SVDBFindIncludedFile;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.utils.SVDBIndexSearcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
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
import org.eclipse.jface.text.BadLocationException;
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
		SVExpressionUtils		expr_utils = new SVExpressionUtils();
		
		SVExprContext expr_ctxt = expr_utils.extractExprContext(scanner, true);
		
		System.out.println("Expression Context: root=" + expr_ctxt.fRoot +
				" trigger=" + expr_ctxt.fTrigger + " leaf=" + expr_ctxt.fLeaf);

		ISVDBIndexIterator index_it = fEditor.getIndexIterator();
		
		
		// Now, iterate through the items in the file and find something
		// with the same name
		SVDBFile file = fEditor.getSVDBFile();
		
		SVDBScopeItem active_scope = SVDBSearchUtils.findActiveScope(
				file, getTextSel().getStartLine());

		List<SVDBItem> items = expr_utils.findItems(index_it, active_scope, expr_ctxt, false);
		
		if (items.size() > 0) {
			it = items.get(0);
		}

		/*
		StringBuffer text = new StringBuffer();

		if (expr_ctxt.fTrigger != null) {
			if (expr_ctxt.fTrigger.equals("`")) {
				if (expr_ctxt.fRoot != null && expr_ctxt.fRoot.equals("include")) {
					SVDBFindIncludedFile finder = new SVDBFindIncludedFile(index_it);
					it = finder.find(expr_ctxt.fLeaf);
				} else {
					// most likely a macro call
					ISVDBItemIterator<SVDBItem> it_i = index_it.getItemIterator();
					while (it_i.hasNext()) {
						SVDBItem it_t = it_i.nextItem();
						
						if (it_t.getType() == SVDBItemType.Macro &&
								it_t.getName().equals(expr_ctxt.fLeaf)) {
							it = it_t;
							break;
						}
					}
				}
			} else {
				List<SVDBItem> pre_trigger = expr_utils.processPreTriggerPortion(
						index_it, active_scope, expr_ctxt.fRoot, false);
				
				if (pre_trigger != null && pre_trigger.size() != 0) {
					SVDBItem it_t = pre_trigger.get(pre_trigger.size()-1);
					
					if (it_t.getType() == SVDBItemType.Class || it_t.getType() == SVDBItemType.Struct) {
						SVDBFindByNameInClassHierarchy finder_h = 
							new SVDBFindByNameInClassHierarchy(index_it);
						List<SVDBItem> fields = finder_h.find(
								(SVDBScopeItem)it_t, expr_ctxt.fLeaf);
						
						if (fields.size() > 0) {
							it = fields.get(0);
						}
					}
				}
			}
		} else {
			// No trigger info. Re-do this search by reading the identifier surrounding
			// the cursor location

			text.setLength(0);
			text.append(expr_ctxt.fLeaf);

			System.out.println("Looking for un-triggered identifier \"" +
					text.toString() + "\"");
			List<SVDBItem> result = null;

			if (it == null) {
				SVDBFindByNameInClassHierarchy finder_h =
					new SVDBFindByNameInClassHierarchy(index_it);

				result = finder_h.find(active_scope, text.toString());

				if (result.size() > 0) {
					it = result.get(0);

					if (result.size() > 1) {
						System.out.println("multiple matches");
						for (SVDBItem it_t : result) {
							System.out.println("    " + it_t.getName());
						}
					}
				}
			} 

			if (it == null) {
				// Try type names
				SVDBFindNamedModIfcClassIfc finder_cls =
					new SVDBFindNamedModIfcClassIfc(index_it);

				it = finder_cls.find(text.toString());

				System.out.println("Class item=" + it);
			}
			
			if (it == null) {
				// Try global task/function
				SVDBFindByName finder_tf = new SVDBFindByName(index_it);
				
				List<SVDBItem> it_l= finder_tf.find(text.toString(), 
						SVDBItemType.Task, SVDBItemType.Function);
				
				if (it_l != null && it_l.size() > 0) {
					it = it_l.get(0);
				}
			}
		}
		 */
		
		if (it != null) {
			IEditorPart ed_f = openEditor(it, fEditor.getIndexIterator());
			((SVEditor)ed_f).setSelection(it, true);
		} else if (inc_file != null) {
			openEditor(inc_file.getFilePath(), fEditor.getIndexIterator());
		}
	}
	
	/**
	 * Search the enclosing scope for tasks, functions, and fields
	 * that match the name
	 * @param scope
	 * @return
	 */
	private SVDBItem searchEnclosingScope(
			String				text,
			SVDBScopeItem 		scope) {
		SVDBItem it = null;
		List<SVDBItem> it_l;

		while (scope != null) {
			it_l = SVDBSearchUtils.findItemsByName(scope, text);
			
			if (it_l.size() > 0) {
				it = it_l.get(0);
				break;
			}
			scope = scope.getParent();
		}
		
		return it;
	}
	
	private SVDBModIfcClassDecl findEnclosingClass(SVDBScopeItem scope) {
		
		while (scope != null && 
				(scope.getType() != SVDBItemType.Class &&
					scope.getType() != SVDBItemType.Module)) {
			scope = scope.getParent();
		}
		
		if (scope != null /* && scope.getType() == SVDBItemType.Class */) {
			return (SVDBModIfcClassDecl)scope;
		} else {
			return null;
		}
	}
	
	private SVDBItem searchClassHierarchy(
			String					name,
			SVDBModIfcClassDecl		enclosing_class,
			ISVDBIndex				index) {
		SVDBItem it = null;
		SVDBIndexSearcher searcher = new SVDBIndexSearcher(index);
		
		while (true) {
			if (enclosing_class.getSuperClass() == null ||
					(enclosing_class = searcher.findNamedModClassIfc(
							enclosing_class.getSuperClass())) == null) {
				break;
			}
			
			List<SVDBItem> r = SVDBSearchUtils.findItemsByName(
					enclosing_class, name);
			
			if (r.size() > 0) {
				it = r.get(0);
				break;
			}
		}
		
		return it;
	}
			
	private SVDBItem findNamedItem(String name, SVDBScopeItem scope) {
		
		if (scope.getName().equals(name)) {
			return scope;
		}
		
		while (scope != null) {
			for (SVDBItem it : scope.getItems()) {
				if (it.getName().equals(name)) {
					return it;
				}
				if (it instanceof SVDBScopeItem) {
					SVDBItem ret = findNamedSubItem(name, (SVDBScopeItem)it);
					
					if (ret != null) {
						return ret;
					}
				}
			}
			
			scope = scope.getParent();
		}
		
		return null;
	}
	
	private SVDBItem findNamedSubItem(String name, SVDBScopeItem scope) {
		if (scope.getName().equals(name)) {
			return scope;
		}
		
		for (SVDBItem it : scope.getItems()) {
			if (it.getName().equals(name)) {
				return it;
			}
			if (it instanceof SVDBScopeItem) {
				SVDBItem ret = findNamedSubItem(name, (SVDBScopeItem)it);
				
				if (ret != null) {
					return ret;
				}
			}
		}
		
		return null;
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

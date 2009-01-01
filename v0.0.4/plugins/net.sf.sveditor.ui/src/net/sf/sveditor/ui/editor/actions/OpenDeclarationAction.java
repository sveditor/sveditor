package net.sf.sveditor.ui.editor.actions;

import java.io.File;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.ISVDBIndex;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.utils.SVDBFileSearcher;
import net.sf.sveditor.core.db.utils.SVDBIndexSearcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.ui.Activator;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorRegistry;
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

	public OpenDeclarationAction(
			ResourceBundle			bundle,
			String					prefix,
			SVEditor				editor) {
		super(bundle, prefix, editor);
		fEditor = editor;
		update();
	}

	@Override
	public void update() {
		// TODO Auto-generated method stub
		super.update();
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
		String text = getTextSel().getText().trim();
		SVDBProjectData pd = fEditor.getProjectData();
		
		// Now, iterate through the items in the file and find something
		// with the same name
		SVDBFile file = fEditor.getSVDBFile();
		SVDBFileSearcher searcher = new SVDBFileSearcher(file);
		
		SVDBScopeItem       active_scope = searcher.findActiveScope(getTextSel().getStartLine());
		SVDBItem			it = null;
		
		// Search up the scope for a matching name
		if (active_scope != null) {
			it = findNamedItem(text, active_scope);
			
			SVDBModIfcClassDecl enclosing_class = null;
			it = searchEnclosingScope(text, active_scope);
		
			if (it == null && pd != null && 
					(enclosing_class = findEnclosingClass(active_scope)) != null &&
					enclosing_class.getSuperClass() != null && 
					!enclosing_class.getSuperClass().equals("")) {
				// TODO: Now, search up the class hierarchy for a match
				it = searchClassHierarchy(text, enclosing_class, pd.getFileIndex());
			}
		}
		
		if (it == null && pd != null) {
			// Search through the indexed files for a matching macro
			// or class declaration
			SVDBIndexSearcher index_search = new SVDBIndexSearcher();
			index_search.addFile(fEditor.getSVDBFile());
			index_search.addIndex(pd.getFileIndex());
			
			List<SVDBItem> result = index_search.findByName(text, 
					SVDBItemType.Class, SVDBItemType.Macro);
			
			if (result.size() > 0) {
				it = result.get(0);
			}
		}
		
		if (it != null) {
			IEditorPart ed_f = openEditor(it);

			((SVEditor)ed_f).setSelection(it.getLocation().getLine(), true);
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
			it_l = SVDBSearchUtils.findItemsByName(scope, text,
				SVDBItemType.Function, SVDBItemType.Task,
				SVDBItemType.TaskFuncParam, SVDBItemType.Macro);
			
			if (it_l.size() > 0) {
				it = it_l.get(0);
				break;
			}
			scope = scope.getParent();
		}
		
		return it;
	}
	
	private SVDBModIfcClassDecl findEnclosingClass(SVDBScopeItem scope) {
		
		while (scope != null && scope.getType() != SVDBItemType.Class) {
			scope = scope.getParent();
		}
		
		if (scope.getType() == SVDBItemType.Class) {
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
					(enclosing_class = searcher.findNamedClass(
							enclosing_class.getSuperClass())) == null) {
				break;
			}
			
			List<SVDBItem> r = SVDBSearchUtils.findItemsByName(
					enclosing_class, name, 
					SVDBItemType.Task, SVDBItemType.Function,
					SVDBItemType.VarDecl);
			
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
		
		for (SVDBItem it : scope.getItems()) {
			if (it.getName().equals(name)) {
				return it;
			}
			if (it instanceof SVDBScopeItem) {
				SVDBItem ret = findNamedItem(name, (SVDBScopeItem)it);
				
				if (ret != null) {
					return ret;
				}
			}
		}
		
		return null;
	}
	
	private IEditorPart openEditor(SVDBItem it) {
		IEditorPart ret = null;
		SVDBItem p = it.getParent();
		IFile f = null;
		// Find the file that this item belongs to
		
		while (p != null && !(p instanceof SVDBFile)) {
			p = p.getParent();
		}
		
		File file = ((SVDBFile)p).getFilePath();
		if (p != null) { 
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IFile f_l[] = root.findFilesForLocation(
					new Path(file.getAbsolutePath()));
			
			if (f_l != null && f_l.length > 0) {
				f = f_l[0];

				IWorkbench wb = PlatformUI.getWorkbench();
				IWorkbenchWindow w = wb.getActiveWorkbenchWindow();

				for (IWorkbenchPage page : w.getPages()) {
					for (IEditorReference ed_r : page.getEditorReferences()) {
						String id = ed_r.getId();
						
						if (!id.equals(Activator.PLUGIN_ID + ".editor")) {
							continue;
						}
						IEditorInput in = null;
						
						try {
							in = ed_r.getEditorInput();
						} catch (PartInitException e) {
							e.printStackTrace();
						}
						
						if (in instanceof FileEditorInput) {
							FileEditorInput in_f = (FileEditorInput)in;
							if (in_f.getPath().equals(f)) {
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
		}
		
		if (ret == null) {
			IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			IEditorRegistry rgy = PlatformUI.getWorkbench().getEditorRegistry();

			IEditorDescriptor desc = rgy.getDefaultEditor(file.getName());
			IEditorInput ed_in = null;
			
			try {
				if (f != null) {
					ed_in = new FileEditorInput(f);
				} else {
					IFileStore fs = EFS.getLocalFileSystem().getStore(file.toURI());
					ed_in = new FileStoreEditorInput(fs);
					
					// TODO: need to connect up index to filesystem
				}
				ret = w.getActivePage().openEditor(ed_in, desc.getId());
			} catch (PartInitException e) {
				e.printStackTrace();
			}
		}
		
		
		return ret;
	}
}

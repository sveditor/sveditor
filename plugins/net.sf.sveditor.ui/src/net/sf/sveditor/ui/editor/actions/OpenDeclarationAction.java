package net.sf.sveditor.ui.editor.actions;

import java.io.File;
import java.util.ResourceBundle;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.ui.Activator;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileStore;
import org.eclipse.core.internal.filebuffers.FileStoreTextFileBuffer;
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
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.FileStoreEditorInput;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
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
		SVDBItem it = findNamedItem(text, file);
		
		if (it == null && pd != null) {
			System.out.println("text=" + text);
			for (SVDBFile f : pd.getFileIndex().getFileList()) {
				for (SVDBItem it_t : f.getItems()) {
					if (it_t.getName() != null && it_t.getName().equals(text)) {
						it = it_t;
						break;
					}
				}
			}
		}

		System.out.println("it=" + it);
		if (it != null) {
			IEditorPart ed_f = openEditor(it);

			((SVEditor)ed_f).setSelection(it.getLocation().getLine(), true);
		}
		
		System.out.println("OpenDefinitionAction.run() - " + text);
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

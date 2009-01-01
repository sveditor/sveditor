package net.sf.sveditor.ui.explorer;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.ui.Activator;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionBars;
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
import org.eclipse.ui.actions.SelectionListenerAction;
import org.eclipse.ui.navigator.CommonActionProvider;
import org.eclipse.ui.navigator.ICommonActionConstants;
import org.eclipse.ui.navigator.ICommonActionExtensionSite;
import org.eclipse.ui.part.FileEditorInput;

public class OpenSVDBItem extends CommonActionProvider {
	private OpenItemAction			fOpenItem;

	@Override
	public void init(ICommonActionExtensionSite site) {
		super.init(site);
		fOpenItem = new OpenItemAction();
	}

	@Override
	public void fillContextMenu(IMenuManager menu) {
		menu.add(fOpenItem);

		fOpenItem.selectionChanged(
				(IStructuredSelection)getContext().getSelection());
				
		super.fillContextMenu(menu);
	}
	
	@Override
	public void fillActionBars(IActionBars actionBars) {
		super.fillActionBars(actionBars);
		actionBars.setGlobalActionHandler(ICommonActionConstants.OPEN, 
				fOpenItem);
		
		fOpenItem.selectionChanged(
				(IStructuredSelection)getContext().getSelection());
	}



	private class OpenItemAction extends SelectionListenerAction {
		
		public OpenItemAction() {
			super("Open");
		}

		@Override
		@SuppressWarnings("unchecked")
		public void run() {
			super.run();
			
			for (SVDBItem it : (List<SVDBItem>)getSelectedNonResources()) {
				IEditorPart ed_f = openEditor(it);

				((SVEditor)ed_f).setSelection(it.getLocation().getLine(), true);
			}
		}
		
		private IEditorPart openEditor(SVDBItem it) {
			IEditorPart ret = null;
			SVDBItem p = it.getParent();
			IFile f = null;
			// Find the file that this item belongs to
			
			while (p != null && !(p instanceof SVDBFile)) {
				p = p.getParent();
			}
			
			if (p != null) {
				File file = ((SVDBFile)p).getFilePath();
				IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
				IFile f_l[] = root.findFilesForLocation(
						new Path(file.getAbsolutePath()));
				
				if (f_l != null && f_l.length > 0) {
					f = f_l[0];

					getActionSite().getViewSite().getShell();
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
				
				IEditorDescriptor desc = rgy.getDefaultEditor(f.getName());
				
				try {
					ret = w.getActivePage().openEditor(new FileEditorInput(f), 
						desc.getId());
				} catch (PartInitException e) {
					e.printStackTrace();
				}
			}
			
			
			return ret;
		}
	}
}

package net.sf.sveditor.ui.editor;

import java.io.File;

import net.sf.sveditor.core.ISVDBFileProvider;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBProjectDataFileProvider;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.part.IShowInTarget;
import org.eclipse.ui.part.ShowInContext;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class SVOutlinePage extends ContentOutlinePage 
	implements IShowInTarget, IAdaptable, 
			Runnable, ILiveSVDBChangeListener {
	private IDocument					fDoc;
	private SVTreeContentProvider		fContentProvider;
	private SVDBFile					fInput;
	private SVEditor					fEditor;
	private boolean						fIgnoreSelection = false;
	private File						fFile;
	
	public SVOutlinePage(SVEditor editor) {
		fEditor = editor;
		fContentProvider = new SVTreeContentProvider();
	}
	
	public void createControl(Composite parent) {
		super.createControl(parent);
		
		fInput = fEditor.getSVDBFile();
		
		fContentProvider = new SVTreeContentProvider();
		
		getTreeViewer().setContentProvider(fContentProvider);
		getTreeViewer().setLabelProvider(new SVTreeLabelProvider());
		
		getTreeViewer().setInput(fInput);
		
		getTreeViewer().getControl().getDisplay().asyncExec(this);
		
		getTreeViewer().addSelectionChangedListener(fSelectionListener);
		getTreeViewer().setAutoExpandLevel(TreeViewer.ALL_LEVELS);
	}
	
	@Override
	public void liveSVDBChanged() {
		if (getTreeViewer() != null) {
			getTreeViewer().getControl().getDisplay().timerExec(1000, this);
		}
	}


	public void run() {
		IEditorInput ed_in = fEditor.getEditorInput();
		String path = ed_in.getName();
		
		ISVDBFileProvider file_p = null;
		if (ed_in instanceof IFileEditorInput) {
			SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBProjectData pdata = null;
			path = ((IFileEditorInput)ed_in).getFile().getLocation().toOSString();
			pdata = mgr.getProjectData(((IFileEditorInput)ed_in).getFile().getProject());
			file_p = new SVDBProjectDataFileProvider(pdata);
		} else if (ed_in instanceof IURIEditorInput) {
			// TODO: could do search for adjacent files
		}
		
		StringInputStream sin = new StringInputStream(fDoc.get());

		// TODO: Need the editor to handle this automatically
		SVDBFile new_in = SVDBFileFactory.createFile(sin, path, file_p);
		
		if (fInput != null) {
			SVDBFileMerger.merge(fInput, new_in, null, null, null);
		} else {
			fInput = new_in;
			getTreeViewer().setInput(fInput);
		}
		
		fInput.setFilePath(fEditor.getFilePath());
		
		SVCorePlugin.getDefault().getSVDBMgr().setLiveSource(fFile, fInput); 
		
		if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
			getTreeViewer().refresh();
		}
	}

	public void dispose() {
		if (getTreeViewer() != null) {
			getTreeViewer().removeSelectionChangedListener(fSelectionListener);
		}
	}

	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		if (IShowInTarget.class.equals(adapter)) {
			return this;
		}
		return null;
	}

	
	public boolean show(ShowInContext context) {
		// TODO Auto-generated method stub
		return true;
	}
	
	private ISelectionChangedListener fSelectionListener = 
		new ISelectionChangedListener() {

			
			public void selectionChanged(SelectionChangedEvent event) {
				if (fIgnoreSelection) {
					return;
				}
				
				removeSelectionChangedListener(this);
				
				if (event.getSelection() instanceof StructuredSelection) {
					StructuredSelection sel = (StructuredSelection)event.getSelection();
					if (sel.getFirstElement() instanceof SVDBItem) {
						SVDBLocation loc = ((SVDBItem)sel.getFirstElement()).getLocation();
						if (loc != null) {
							fEditor.setSelection(loc.getLine());
						}
					}
				}
				
				addSelectionChangedListener(this);
			}
	};
	
}

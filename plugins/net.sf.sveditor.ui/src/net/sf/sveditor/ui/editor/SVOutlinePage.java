package net.sf.sveditor.ui.editor;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.ISVDBChangeListener;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBWorkspaceFileManager;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.IShowInTarget;
import org.eclipse.ui.part.ShowInContext;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class SVOutlinePage extends ContentOutlinePage 
	implements IShowInTarget, IAdaptable, 
			Runnable, ISVDBChangeListener {
	private SVTreeContentProvider		fContentProvider;
	private SVEditor					fEditor;
	private boolean						fIgnoreSelection = false;
	private SVDBWorkspaceFileManager	fFileManager;
	
	public SVOutlinePage(SVEditor editor) {
		fEditor = editor;
		fContentProvider = new SVTreeContentProvider();
	}
	
	public void createControl(Composite parent) {
		super.createControl(parent);
		
		fContentProvider = new SVTreeContentProvider();
		
		getTreeViewer().setContentProvider(fContentProvider);
		getTreeViewer().setLabelProvider(new SVTreeLabelProvider());
		
		getTreeViewer().setInput(fEditor.getSVDBFile());
		
		getTreeViewer().getControl().getDisplay().asyncExec(this);
		
		getTreeViewer().addSelectionChangedListener(fSelectionListener);
		getTreeViewer().setAutoExpandLevel(TreeViewer.ALL_LEVELS);
		
		fFileManager = SVCorePlugin.getDefault().getSVDBMgr();
		fFileManager.addSVDBChangeListener(this);
	}

	
	public void SVDBFileChanged(SVDBFile file, List<SVDBItem> adds,
			List<SVDBItem> removes, List<SVDBItem> changes) {
		if (file.getFilePath().equals(fEditor.getFilePath())) {
			if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
				getTreeViewer().getControl().getDisplay().timerExec(1000, this);
			}
		}
	}

	public void run() {
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

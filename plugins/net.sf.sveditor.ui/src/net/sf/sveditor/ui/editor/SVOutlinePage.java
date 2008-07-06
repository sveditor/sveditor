package net.sf.sveditor.ui.editor;

import java.io.File;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.IShowInTarget;
import org.eclipse.ui.part.ShowInContext;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class SVOutlinePage extends ContentOutlinePage 
	implements IDocumentListener, IShowInTarget, IAdaptable, Runnable {
	private IDocument					fDoc;
	private SVTreeContentProvider		fContentProvider;
	private SVDBFile					fInput;
	private SVEditor					fEditor;
	private boolean						fIgnoreSelection = false;
	
	public SVOutlinePage(SVEditor editor) {
		fEditor = editor;
		fDoc = fEditor.getDocumentProvider().getDocument(
				fEditor.getEditorInput());
		fDoc.addDocumentListener(this);
		fContentProvider = new SVTreeContentProvider();
	}
	
	@Override
	public void createControl(Composite parent) {
		super.createControl(parent);
		
		fInput = new SVDBFile(new File(""));
		
		fContentProvider = new SVTreeContentProvider();
		
		getTreeViewer().setContentProvider(fContentProvider);
		getTreeViewer().setLabelProvider(new SVTreeLabelProvider());
		
		getTreeViewer().setInput(fInput);
		
		getTreeViewer().getControl().getDisplay().asyncExec(this);
		
		getTreeViewer().addSelectionChangedListener(fSelectionListener);
		getTreeViewer().setAutoExpandLevel(TreeViewer.ALL_LEVELS);
	}

	@Override
	public void documentAboutToBeChanged(DocumentEvent event) {}

	@Override
	public void documentChanged(DocumentEvent event) {
		if (getTreeViewer() != null) {
			getTreeViewer().getControl().getDisplay().timerExec(1000, this);
		}
	}
	
	public void run() {
		StringInputStream sin = new StringInputStream(fDoc.get());
		
		SVDBFile new_in = SVDBFileFactory.createFile(sin, "foo");
		
		if (fInput != null) {
			SVDBFileMerger.merge(fInput, new_in, null, null, null);
		} else {
			fInput = new_in;
			getTreeViewer().setInput(fInput);
		}
		
		getTreeViewer().refresh();
	}

	public void dispose() {
		fDoc.removeDocumentListener(this);
		getTreeViewer().removeSelectionChangedListener(fSelectionListener);
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		if (IShowInTarget.class.equals(adapter)) {
			return this;
		}
		return null;
	}

	@Override
	public boolean show(ShowInContext context) {
		// TODO Auto-generated method stub
		return true;
	}
	
	private ISelectionChangedListener fSelectionListener = 
		new ISelectionChangedListener() {

			@Override
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

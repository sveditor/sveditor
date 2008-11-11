package net.sf.sveditor.ui.editor;

import java.io.File;
import java.net.URI;
import java.util.ResourceBundle;

import net.sf.sveditor.core.ISVDBFileProvider;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBProjectDataFileProvider;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.ui.Activator;

import org.eclipse.core.runtime.ListenerList;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.editors.text.ITextEditorHelpContextIds;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.ide.IDEActionFactory;
import org.eclipse.ui.texteditor.AddTaskAction;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class SVEditor extends TextEditor {
	private ListenerList				fReconcileListeners;
	private SVOutlinePage				fOutline;
	private SVHighlightingManager		fHighlightManager;
	private SVCodeScanner					fCodeScanner;

	public SVEditor() {
		super();
		
		fReconcileListeners = new ListenerList();
		setDocumentProvider(SVEditorDocumentProvider.getDefault());
		
		fCodeScanner = new SVCodeScanner();
	}
	
	public SVCodeScanner getCodeScanner() {
		return fCodeScanner;
	}
	
	protected void initializeEditor() {
		super.initializeEditor();
	}
	
	@Override
	protected void createActions() {
		// TODO Auto-generated method stub
		super.createActions();

		ResourceBundle bundle = Activator.getDefault().getResources();
		IAction a = new TextOperationAction(bundle,
				"ContentAssistProposal.", this,
				ISourceViewer.CONTENTASSIST_PROPOSALS);

		// Added this call for 2.1 changes
		// New to 2.1 - CTRL+Space key doesn't work without making this call
		a.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS);
		setAction("ContentAssistProposal", a);

		a = new TextOperationAction(bundle, "ContentAssistTip.",
				this, ISourceViewer.CONTENTASSIST_CONTEXT_INFORMATION);

		//	Added this call for 2.1 changes
		a.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_CONTEXT_INFORMATION);
		setAction("ContentAssistTip", a);

		a = new TextOperationAction(bundle,
				"ContentFormatProposal.", this, ISourceViewer.FORMAT);
		setAction("ContentFormatProposal", a);

		// Add the task action to the Edit pulldown menu (bookmark action is
		// 'free')
		ResourceAction ra = new AddTaskAction(bundle, "AddTask.",
				this);
		ra.setHelpContextId(ITextEditorHelpContextIds.ADD_TASK_ACTION);
		ra.setActionDefinitionId(ITextEditorActionDefinitionIds.ADD_TASK);
		setAction(IDEActionFactory.ADD_TASK.getId(), ra);

		//Add action to define the marked area as a folding area
		/*
		a = new DefineFoldingRegionAction(bundle,
				"DefineFoldingRegion.", this); //$NON-NLS-1$
		setAction("DefineFoldingRegion", a);
		 */
		
		OpenDeclarationAction od_action = new OpenDeclarationAction(
				bundle, "OpenDeclaration.", this);
		od_action.setActionDefinitionId("net.sf.sveditor.ui.editor.open.declaration");
		setAction("net.sf.sveditor.ui.svOpenEditorAction", od_action);
	}

	protected void editorContextMenuAboutToShow(IMenuManager menu) {
		// TODO Auto-generated method stub
		super.editorContextMenuAboutToShow(menu);
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				"net.sf.sveditor.ui.svOpenEditorAction");
	}

	@Override
	public void dispose() {
		super.dispose();
		
		if (fOutline != null) {
			fOutline.dispose();
			fOutline = null;
		}
	}

	public void createPartControl(Composite parent) {
		setSourceViewerConfiguration(new SVSourceViewerConfiguration(this));
		
		super.createPartControl(parent);
		
		if (fHighlightManager == null) {
			fHighlightManager = new SVHighlightingManager();
			fHighlightManager.install(
					(SourceViewer)getSourceViewer(),
					(SVPresentationReconciler)getSourceViewerConfiguration().getPresentationReconciler(getSourceViewer()),
					this);
		}
		
		fOutline = new SVOutlinePage(this);
		
		/**
		 * Add semantic highlighting
		 */
		
	}
	
	public SVDBFile getSVDBFile() {
		return fOutline.getSVDBFile();
	}
	
	public File getFilePath() {
		IEditorInput ed_in = getEditorInput();
		File ret = null;
		
		if (ed_in instanceof IFileEditorInput) {
			ret = ((IFileEditorInput)ed_in).getFile().getLocation().toFile();
		} else if (ed_in instanceof IURIEditorInput) {
			ret = new File(((IURIEditorInput)ed_in).getURI().getPath());
		}
		
		return ret;
	}
	
	public void setSelection(int lineno) {
		setSelection(lineno, false);
	}
	
	public void setSelection(int lineno, boolean set_cursor) {
		IDocument doc = getDocumentProvider().getDocument(getEditorInput());
		try {
			int offset = doc.getLineOffset(lineno);
			setHighlightRange(offset, 1, false);
			if (set_cursor) {
				getSourceViewer().getTextWidget().setCaretOffset(offset);
			}
			getSourceViewer().revealRange(offset, 1);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		if (adapter.equals(IContentOutlinePage.class)) {
			if (fOutline == null) {
				fOutline = new SVOutlinePage(this);
			}
			return fOutline;
		}
		return super.getAdapter(adapter);
	}
}

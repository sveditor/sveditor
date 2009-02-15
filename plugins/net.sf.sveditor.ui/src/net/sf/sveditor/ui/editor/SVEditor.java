package net.sf.sveditor.ui.editor;

import java.io.File;
import java.net.URI;
import java.util.ResourceBundle;

import net.sf.sveditor.core.ISVDBFileProvider;
import net.sf.sveditor.core.ISVDBIndex;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBProjectDataFileProvider;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.ui.Activator;
import net.sf.sveditor.ui.editor.actions.OpenDeclarationAction;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.ISourceViewerExtension2;
import org.eclipse.jface.text.source.MatchingCharacterPainter;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.ITextEditorHelpContextIds;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.ide.IDEActionFactory;
import org.eclipse.ui.texteditor.AddTaskAction;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class SVEditor extends TextEditor implements IDocumentListener {

	// private ListenerList					fReconcileListeners;
	private SVOutlinePage					fOutline;
	private SVHighlightingManager			fHighlightManager;
	private SVCodeScanner					fCodeScanner;
	private MatchingCharacterPainter		fMatchingCharacterPainter;
	private SVCharacterPairMatcher			fCharacterMatcher;
	private SVDBProjectData					fProjectData;
	private SVDBFile						fSVDBFile;
	private File							fFile;
	private int								fFirstModLine;
	private int								fNumModLines;

	public SVEditor() {
		super();
		
//		fReconcileListeners = new ListenerList();
		setDocumentProvider(SVEditorDocumentProvider.getDefault());
		
		fCodeScanner = new SVCodeScanner();
		fCharacterMatcher = new SVCharacterPairMatcher();
	}
	
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		// TODO Auto-generated method stub
		super.init(site, input);
		
		if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			fFile = new File(uri.getPath()); 
		} else if (input instanceof IFileEditorInput) {
			fFile = ((IFileEditorInput)input).getFile().getLocation().toFile();
		}
		
		fSVDBFile = new SVDBFile(fFile);
		
		getDocumentProvider().getDocument(input).addDocumentListener(this);
		
		// Perform an initial parse of the file
		updateSVDBFile();
	}

	@Override
	public void doSave(IProgressMonitor progressMonitor) {
		super.doSave(progressMonitor);
		
		// TODO: When the user saves the file, clear any cached information
		// on validity.
		
	}
	
	public ITextViewer getTextViewer() {
		return getSourceViewer();
	}

	@Override
	public void doSaveAs() {
		super.doSaveAs();
		
		// TODO: Probably need to make some updates when the name changes
	}

	private void updateSVDBFile() {
		IEditorInput ed_in = getEditorInput();
		IDocument doc = getDocumentProvider().getDocument(ed_in);
		String path = ed_in.getName();

		SVPreProcDefineProvider		def_p = null;
		if (ed_in instanceof IURIEditorInput) {
			SVDBProjectData pdata  = null;
			IURIEditorInput uri_in = (IURIEditorInput)ed_in;
			SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IContainer c[] = root.findContainersForLocationURI(uri_in.getURI());
			
			if (c != null && c.length > 0) {
				pdata = mgr.getProjectData(c[0].getProject());
				ISVDBIndex index = pdata.getFileIndex();
				def_p = new SVPreProcDefineProvider(index);
				
				def_p.setFileContext(index.getFileTree().get(c[0].getLocation().toFile()));
			}
		}
		
		StringInputStream sin = new StringInputStream(doc.get());

		// TODO: Need the editor to handle this automatically
		SVDBFile new_in = SVDBFileFactory.createFile(sin, path, def_p);
		
		SVDBFileMerger.merge(fSVDBFile, new_in, null, null, null);
		
		fSVDBFile.setFilePath(getFilePath());

		if (ed_in instanceof IFileEditorInput) {
			SVCorePlugin.getDefault().getSVDBMgr().setLiveSource(
					((IFileEditorInput)ed_in).getFile(), fSVDBFile);
		}
	}


	public SVCodeScanner getCodeScanner() {
		return fCodeScanner;
	}

	protected void initializeEditor() {
		super.initializeEditor();
	}

	@Override
	protected void initializeKeyBindingScopes() {
		setKeyBindingScopes(new String[] {Activator.PLUGIN_ID + ".svEditorContext"});
	}

	@Override
	protected void createActions() {
		// TODO Auto-generated method stub
		super.createActions();

		ResourceBundle bundle = Activator.getDefault().getResources();
		
		/*
		Action action = new ContentAssistAction(bundle, "ContentAssistProposal.", this);
		String id = ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS;
		action.setActionDefinitionId(id);
		setAction("ContentAssistProposal", action);
		markAsStateDependentAction("ContentAssistProposal", true);
		 */
		
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
		od_action.setActionDefinitionId(Activator.PLUGIN_ID + ".editor.open.declaration");
		setAction(Activator.PLUGIN_ID + ".svOpenEditorAction", od_action);
	}
	
	public SVDBProjectData getProjectData() {
		if (fProjectData == null) {
			File file = getFilePath();
			
			IFile files[] = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(file.toURI());
			
			if (files != null && files.length > 0) {
				SVDBProjectManager pm = SVCorePlugin.getDefault().getProjMgr();
				fProjectData = pm.getProjectData(files[0].getProject());
			} else {
				// Create an empty project data
				System.out.println("[FIXME] create an empty SVProjectData item");
			}
		}
		
		return fProjectData;
	}
	
	public void setProjectData(SVDBProjectData pd) {
		fProjectData = pd;
	}

	protected void editorContextMenuAboutToShow(IMenuManager menu) {
		// TODO Auto-generated method stub
		super.editorContextMenuAboutToShow(menu);
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				Activator.PLUGIN_ID + ".svOpenEditorAction");
	}
	
	@Override
	public void dispose() {
		super.dispose();
		
//		getDocumentProvider().getDocument(getEditorInput()).removeDocumentListener(this);
		
		if (fOutline != null) {
			fOutline.dispose();
			fOutline = null;
		}
		if (fCharacterMatcher != null) {
			fCharacterMatcher.dispose();
			fCharacterMatcher = null;
		}
		
		SVCorePlugin.getDefault().getSVDBMgr().removeLiveSource(fFile);
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
		
//		fOutline = new SVOutlinePage(this);
		
		// Setup matching character highligher
		if (fMatchingCharacterPainter == null) {
			if (getSourceViewer() instanceof ISourceViewerExtension2) {
				fMatchingCharacterPainter = new MatchingCharacterPainter(
						getSourceViewer(), fCharacterMatcher);
				Display display = Display.getCurrent();
				
				// TODO: reference preference store
				fMatchingCharacterPainter.setColor(display.getSystemColor(SWT.COLOR_GRAY));
				((ITextViewerExtension2)getSourceViewer()).addPainter(
						fMatchingCharacterPainter);
			}
		}
		
		
		/**
		 * Add semantic highlighting
		 */
		
	}

	public SVDBFile getSVDBFile() {
		return fSVDBFile;
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
		
		// Lineno is used as an offset
		if (lineno > 0) {
			lineno--;
		}
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

	public void documentAboutToBeChanged(DocumentEvent event) {
		/*
		System.out.println("--> documentChanged");
		IDocument doc = event.fDocument;
		int change_new_offset = event.fText.length() - event.fLength;
		int old_end_offset = event.fOffset + event.fLength;
		int new_end_offset = event.fOffset + event.fText.length();
		
		int start_line = -1;
		int old_end_line = -1;
		int new_end_line = -1;
		
		try {
			start_line = doc.getLineOfOffset(event.fOffset);
		} catch (Exception e) { }
		
		try {
			old_end_line = doc.getLineOfOffset(old_end_offset);
		} catch (Exception e) { }
		
		try {
			new_end_line = doc.getLineOfOffset(new_end_offset);
		} catch (Exception e) { }
		
		System.out.println("start_line=" + start_line);
		System.out.println("old_end_line=" + old_end_line);
		System.out.println("new_end_line=" + new_end_line);
		
		System.out.println("change start offset=" + event.fOffset + " length=" + event.fLength);
		System.out.println("change=" + event.fText);
		try {
			int end_line = doc.getLineOfOffset(event.fOffset+event.fLength);
			System.out.println("starts @ " + start_line + " ends @ " + end_line);
		} catch (Exception e) {
			e.printStackTrace();
		}
		System.out.println("<-- documentChanged");
		 */
	}

	public void documentChanged(DocumentEvent event) {
		/*
		String doc_s = getDocumentProvider().getDocument(getEditorInput()).toString();
		StringInputStream in = new StringInputStream(doc_s);
		SVDBFile file = SVDBFileFactory.createFile(in, fFile.getName());
		 */
		updateSVDBFile();
	}
}

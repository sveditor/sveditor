package net.sf.sveditor.ui.editor;

import java.io.File;
import java.net.URI;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.index.src_collection.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.db.project.ISVDBProjectSettingsListener;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.actions.OpenDeclarationAction;
import net.sf.sveditor.ui.editor.actions.OverrideTaskFuncAction;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.ISourceViewerExtension2;
import org.eclipse.jface.text.source.MatchingCharacterPainter;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
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
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AddTaskAction;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class SVEditor extends TextEditor 
	implements ISVDBProjectSettingsListener {

	private SVOutlinePage					fOutline;
	private SVHighlightingManager			fHighlightManager;
	private SVCodeScanner					fCodeScanner;
	private MatchingCharacterPainter		fMatchingCharacterPainter;
	private SVCharacterPairMatcher			fCharacterMatcher;
	private SVDBProjectData					fProjectData;
	private SVDBFile						fSVDBFile;
	private ISVDBIndex						fSVDBIndex;
	private String							fFile;
	private SVDBIndexCollectionMgr			fIndexMgr;
	private LogHandle						fLog;
	private String							fSVDBFilePath;

	
	public SVEditor() {
		super();
		
		setDocumentProvider(SVEditorDocumentProvider.getDefault());
		
		fCodeScanner = new SVCodeScanner();
		fCharacterMatcher = new SVCharacterPairMatcher();
		SVUiPlugin.getDefault().getPreferenceStore().addPropertyChangeListener(
				fPropertyChangeListener);
		
		fLog = LogFactory.getDefault().getLogHandle("SVEditor");
	}
	
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		// TODO Auto-generated method stub
		super.init(site, input);
		
		if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			if (uri.getScheme().equals("plugin")) {
				fFile = "plugin:" + uri.getPath();
			} else {
				fFile = uri.getPath();
			}
		} else if (input instanceof IFileEditorInput) {
			fFile = ((IFileEditorInput)input).getFile().getFullPath().toOSString();
		}
		
		fSVDBFile = new SVDBFile(fFile);
		
		// Hook into the SVDB management structure
		initSVDBMgr();
		
		// Perform an initial parse of the file
		updateSVDBFile();
	}

	@Override
	public void doSave(IProgressMonitor progressMonitor) {
		super.doSave(progressMonitor);
		
		// TODO: When the user saves the file, clear any cached information
		// on validity.
		
	}

	/*
	public ITextViewer getTextViewer() {
		return getSourceViewer();
	}
	 */

	@Override
	public void doSaveAs() {
		super.doSaveAs();
		
		// TODO: Probably need to make some updates when the name changes
	}

	/**
	 * Called when project settings change. Update our notion of
	 * which index is managing this file
	 */
	public void projectSettingsChanged(SVDBProjectData data) {
		fLog.debug("Updating index information for editor \"" + 
				fSVDBFilePath + "\"");
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		List<SVDBSearchResult<SVDBFile>> result;
		if ((result = fIndexMgr.findPreProcFile(fSVDBFilePath)).size() == 0) {
			fLog.debug("Create a shadow index for \"" + fSVDBFilePath + "\"");
			fSVDBIndex = rgy.findCreateIndex(data.getName(),
					new File(fSVDBFilePath).getParent(),
					SVDBSourceCollectionIndexFactory.TYPE, null);
			fIndexMgr.addShadowIndex(fSVDBIndex.getBaseLocation(), fSVDBIndex);
		} else {
			fLog.debug("File \"" + fSVDBFilePath + "\" is in index \"" + 
					result.get(0).getIndex().getBaseLocation() + 
					"\" (" + result.size() + " results)");
			fSVDBIndex = result.get(0).getIndex();
			if (result.size() > 1) {
				for (SVDBSearchResult<SVDBFile> r : result) {
					fLog.debug("    " + r.getIndex().getBaseLocation());
				}
			}
		}
	}

	private void initSVDBMgr() {
		IEditorInput ed_in = getEditorInput();
		
		if (ed_in instanceof IURIEditorInput) {
			fProjectData = null;
			IURIEditorInput uri_in = (IURIEditorInput)ed_in;
			SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();

			if (uri_in.getURI().getScheme().equals("plugin")) {
				fLog.debug("Editor path is in a plugin: " + uri_in.getURI());
				fSVDBFilePath = "plugin:" + uri_in.getURI().getPath();
				
				SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
				SVDBPluginLibDescriptor target = null;
				
				String uri_path = uri_in.getURI().getPath();
				String plugin = uri_path.substring(1, uri_path.indexOf('/', 1));
				String root_file = uri_path.substring(uri_path.indexOf('/', 1));
				
				for (SVDBPluginLibDescriptor d : SVCorePlugin.getDefault().getPluginLibList()) {
					if (d.getNamespace().equals(plugin)) {
						String root_dir = new File(d.getPath()).getParent();
						if (!root_dir.startsWith("/")) {
							root_dir = "/" + root_dir;
						}
						
						if (root_file.startsWith(root_dir)) {
							target = d;
							break;
						}
					}
				}
				
				fIndexMgr = new SVDBIndexCollectionMgr(plugin);

				if (target != null) {
					fLog.debug("Found a target plugin library");
					fIndexMgr.addPluginLibrary(rgy.findCreateIndex("GLOBAL", 
							target.getId(), SVDBPluginLibIndexFactory.TYPE, null));
				} else {
					fLog.debug("Did not find the target plugin library");
				}
			} else { // regular workspace or filesystem path
				SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
				if (ed_in instanceof FileEditorInput) {
					FileEditorInput fi = (FileEditorInput)ed_in;
					fLog.debug("Path \"" + fi.getFile().getFullPath() + 
							"\" is in project " + fi.getFile().getProject().getName());
					
					fProjectData = mgr.getProjectData(fi.getFile().getProject());
					fProjectData.addProjectSettingsListener(this);
					
					fIndexMgr = fProjectData.getProjectIndexMgr();
					fSVDBFilePath = "${workspace_loc}" + fi.getFile().getFullPath().toOSString();
					
					projectSettingsChanged(fProjectData);
				} else {
					// Create an index manager for this directory
					fSVDBFilePath = uri_in.getURI().getPath();
					fLog.debug("File \"" + fSVDBFilePath + "\" is outside the workspace");
					File fs_path = new File(fSVDBFilePath);
					
					fIndexMgr = null;
					
					for (SVDBProjectData pd : mgr.getProjectList()) {
						SVDBIndexCollectionMgr index_mgr = pd.getProjectIndexMgr();
						List<SVDBSearchResult<SVDBFile>> result;
					
						result = index_mgr.findPreProcFile(fSVDBFilePath);
						
						fLog.debug("Searching for \"" + fSVDBFilePath + "\" in project " +
								pd.getName() + ": " + result.size() + " results");
						
						if (result.size() != 0) {
							fIndexMgr = index_mgr;
							fSVDBIndex = result.get(0).getIndex();
							fLog.debug("File will be managed by index \"" + fSVDBIndex.getBaseLocation() + "\"");
							break;
						}
					}

					if (fIndexMgr == null) {
						fLog.debug("Creating temporary source collection manager");
						fIndexMgr = new SVDBIndexCollectionMgr(fs_path.getParent());
						fSVDBIndex = rgy.findCreateIndex(
								fs_path.getParent(), fs_path.getParent(),
								SVDBSourceCollectionIndexFactory.TYPE, null);
						fIndexMgr.addSourceCollection(fSVDBIndex);
					}
					
					
					// TODO: add default plugin and global libraries
				}
			}
			
		} else {
			fLog.error("SVEditor input is of type " + ed_in.getClass().getName());
		}
	}

	void updateSVDBFile() {
		IEditorInput ed_in = getEditorInput();
		IDocument doc = getDocumentProvider().getDocument(ed_in);
		
		StringInputStream sin = new StringInputStream(doc.get());

		SVDBFile new_in = fIndexMgr.parse(sin, fSVDBFilePath);
		SVDBFileMerger.merge(fSVDBFile, new_in, null, null, null);
		
		fSVDBFile.setFilePath(fSVDBFilePath);
		
		if (fOutline != null) {
			fOutline.refresh();
		}
	}
	
	public SVCodeScanner getCodeScanner() {
		return fCodeScanner;
	}

	@Override
	protected void initializeKeyBindingScopes() {
		setKeyBindingScopes(new String[] {SVUiPlugin.PLUGIN_ID + ".svEditorContext"});
	}

	@SuppressWarnings("deprecation")
	@Override
	protected void createActions() {
		// TODO Auto-generated method stub
		super.createActions();

		ResourceBundle bundle = SVUiPlugin.getDefault().getResources();
		
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
				"Format.", this, ISourceViewer.FORMAT);
		a.setActionDefinitionId("net.sveditor.ui.indent");
		setAction("Format", a);
		markAsStateDependentAction("Format", true);
		markAsSelectionDependentAction("Format", true);

		
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
		od_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.declaration");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", od_action);

		OverrideTaskFuncAction ov_tf_action = new OverrideTaskFuncAction(
				bundle, "OverrideTaskFunc.", this);
		ov_tf_action.setActionDefinitionId(
				SVUiPlugin.PLUGIN_ID + ".override.tf.command");
		setAction(SVUiPlugin.PLUGIN_ID + ".override.tf", ov_tf_action);

	}
	
	private ISVDBIndexIterator SVEditorIndexIterator = new ISVDBIndexIterator() {
		
		public ISVDBItemIterator<SVDBItem> getItemIterator() {
			SVDBIndexCollectionItemIterator it = 
				(SVDBIndexCollectionItemIterator)fIndexMgr.getItemIterator();
			
			it.setOverride(fSVDBIndex, fSVDBFile);
			
			return it;
		}
	};
	
	public ISVDBIndexIterator getIndexIterator() {
		return SVEditorIndexIterator;
	}

	protected void editorContextMenuAboutToShow(IMenuManager menu) {
		super.editorContextMenuAboutToShow(menu);
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction");
		
		/*
		addGroup(menu, ITextEditorActionConstants.GROUP_EDIT, 
				Activator.PLUGIN_ID + ".source.menu");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				"net.sf.sveditor.ui.source.menu.as");
		 */
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT, 
				"net.sf.sveditor.ui.override.tf");
		/*
		addGroup(menu, ITextEditorActionConstants.GROUP_EDIT, 
				"net.sf.sveditor.ui.source.menu.as");
		
		IMenuManager editMenu = menu.findMenuUsingPath(
				IWorkbenchActionConstants.M_EDIT);
		
		System.out.println("editMenu=" + editMenu);
		 */
	}
	
	@Override
	public void dispose() {
		super.dispose();
		
		if (fOutline != null) {
			fOutline.dispose();
			fOutline = null;
		}
		if (fCharacterMatcher != null) {
			fCharacterMatcher.dispose();
			fCharacterMatcher = null;
		}
		
		if (fProjectData != null) {
			fProjectData.removeProjectSettingsListener(this);
		}
		
		SVUiPlugin.getDefault().getPreferenceStore().removePropertyChangeListener(
				fPropertyChangeListener);
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
	
	public String getFilePath() {
		IEditorInput ed_in = getEditorInput();
		String ret = null;
		
		if (ed_in instanceof IFileEditorInput) {
			ret = ((IFileEditorInput)ed_in).getFile().getFullPath().toOSString();
		} else if (ed_in instanceof IURIEditorInput) {
			ret = ((IURIEditorInput)ed_in).getURI().getPath();
		}
		
		return ret;
	}
	
	public void setSelection(SVDBItem it, boolean set_cursor) {
		int start = -1;
		int end   = -1;
		
		if (it.getLocation() != null) {
			start = it.getLocation().getLine();
			
			if (it instanceof SVDBScopeItem &&
					((SVDBScopeItem)it).getEndLocation() != null) {
				end = ((SVDBScopeItem)it).getEndLocation().getLine();
			}
			setSelection(start, end, set_cursor);
		}
	}
	
	public void setSelection(int start, int end, boolean set_cursor) {
		IDocument doc = getDocumentProvider().getDocument(getEditorInput());
		
		// Lineno is used as an offset
		if (start > 0) {
			start--;
		}
		
		if (end == -1) {
			end = start;
		}
		try {
			int offset   = doc.getLineOffset(start);
			int offset_e = doc.getLineOffset(end); 
			setHighlightRange(offset, (offset_e-offset), false);
			if (set_cursor) {
				getSourceViewer().getTextWidget().setCaretOffset(offset);
			}
			getSourceViewer().revealRange(offset, (offset_e-offset));
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
	
	private IPropertyChangeListener fPropertyChangeListener = 
		new IPropertyChangeListener() {

			public void propertyChange(PropertyChangeEvent event) {
				SVColorManager.clear();
				getCodeScanner().updateRules();
				getSourceViewer().getTextWidget().redraw();
				getSourceViewer().getTextWidget().update();
			}
	};

}

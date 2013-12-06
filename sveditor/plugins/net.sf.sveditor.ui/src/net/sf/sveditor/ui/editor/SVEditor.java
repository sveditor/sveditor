/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import java.io.File;
import java.net.URI;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.ResourceBundle;
import java.util.Set;
import java.util.regex.Pattern;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBEndLocation;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBUnprocessedRegion;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBIndexParse;
import net.sf.sveditor.core.db.index.SVDBFileOverrideIndex;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBShadowIncludeFilesFinder;
import net.sf.sveditor.core.db.index.SVDBShadowIndexParse;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.project.ISVDBProjectSettingsListener;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.actions.AddBlockCommentAction;
import net.sf.sveditor.ui.editor.actions.FindReferencesAction;
import net.sf.sveditor.ui.editor.actions.IndentAction;
import net.sf.sveditor.ui.editor.actions.NextWordAction;
import net.sf.sveditor.ui.editor.actions.OpenDeclarationAction;
import net.sf.sveditor.ui.editor.actions.OpenDiagForSelectionAction;
import net.sf.sveditor.ui.editor.actions.OpenObjectsViewAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickHierarchyAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickObjectsViewAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickOutlineAction;
import net.sf.sveditor.ui.editor.actions.OpenTypeAction;
import net.sf.sveditor.ui.editor.actions.OpenTypeHierarchyAction;
import net.sf.sveditor.ui.editor.actions.OverrideTaskFuncAction;
import net.sf.sveditor.ui.editor.actions.PrevWordAction;
import net.sf.sveditor.ui.editor.actions.RemoveBlockCommentAction;
import net.sf.sveditor.ui.editor.actions.SVRulerAnnotationAction;
import net.sf.sveditor.ui.editor.actions.SelNextWordAction;
import net.sf.sveditor.ui.editor.actions.SelPrevWordAction;
import net.sf.sveditor.ui.editor.actions.ToggleCommentAction;
import net.sf.sveditor.ui.editor.outline.SVOutlinePage;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.information.IInformationPresenter;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.ISourceViewerExtension2;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.text.source.MatchingCharacterPainter;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionSupport;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.IWorkbenchPart;
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
	implements ISVDBProjectSettingsListener, ISVEditor, ILogLevel, 
			ISVDBIndexChangeListener, IResourceChangeListener,
			IPartListener {

	private SVOutlinePage					fOutline;
	private SVHighlightingManager			fHighlightManager;
	private SVCodeScanner					fCodeScanner;
	private MatchingCharacterPainter		fMatchingCharacterPainter;
	private SVCharacterPairMatcher			fCharacterMatcher;
	
	// Holds the current parsed AST view of the file
	private SVDBFile						fSVDBFile;
	
	// Holds the current parsed AST pre-processor view of the file
	private SVDBFile						fSVDBFilePP;
	
	// Holds the current list of markers from the file
	private List<SVDBMarker>				fMarkers;
	
	private String							fFile;
	
	// The FileIndexParser is responsible for parsing file content
	// in a way consistent with the containing scope
	private ISVDBIndexParse					fFileIndexParser;

	// The SVDBIndex is responsible for providing a merged view 
	// of this and the containing index to clients, including
	// content assist
	private SVDBFileOverrideIndex			fSVDBIndex;
	
	private LogHandle						fLog;
	private String							fSVDBFilePath;
	private UpdateProjectSettingsJob		fProjectSettingsJob;
	private SVDBProjectData					fPendingProjectSettingsUpdate;
	private UpdateSVDBFileJob				fUpdateSVDBFileJob;
	private boolean							fPendingUpdateSVDBFile;
	private boolean							fNeedUpdate;
	private boolean							fOccurrenceHighlightDebounceActive;
	
	private Map<String, Boolean>			fFoldingPrefs = new HashMap<String, Boolean>();
	
	IInformationPresenter fQuickObjectsPresenter;
	IInformationPresenter fQuickOutlinePresenter;
	IInformationPresenter fQuickHierarchyPresenter;
	
	private ProjectionSupport				fProjectionSupport;
	private boolean							fInitialFolding = true;
	private int								fReparseDelay;
	private boolean							fIncrReparseEn = false;
	
	public ISVDBIndex getSVDBIndex() {
		return fSVDBIndex ;
	}
	
	public IInformationPresenter getQuickObjectsPresenter() {
		if(fQuickObjectsPresenter == null) {
			fQuickObjectsPresenter = 
					((SVSourceViewerConfiguration)getSourceViewerConfiguration())
					.getObjectsPresenter(getSourceViewer(), false) ;
			if(fQuickObjectsPresenter != null) {
				fQuickObjectsPresenter.install(getSourceViewer()) ;
			}
		}
		return fQuickObjectsPresenter ;
	}
	
	public IInformationPresenter getQuickOutlinePresenter() {
		if(fQuickOutlinePresenter == null) {
			fQuickOutlinePresenter = 
					((SVSourceViewerConfiguration)getSourceViewerConfiguration())
					.getOutlinePresenter(getSourceViewer(), false) ;
			if(fQuickOutlinePresenter != null) {
				fQuickOutlinePresenter.install(getSourceViewer()) ;
			}
		}
		return fQuickOutlinePresenter ;
	}
	
	public IInformationPresenter getQuickHierarchyPresenter() {
		if(fQuickHierarchyPresenter == null) {
			fQuickHierarchyPresenter = 
					((SVSourceViewerConfiguration)getSourceViewerConfiguration())
					.getHierarchyPresenter(getSourceViewer(), false) ;
			if(fQuickHierarchyPresenter != null) {
				fQuickHierarchyPresenter.install(getSourceViewer()) ;
			}
		}
		return fQuickHierarchyPresenter ;
	}
	
	
	private class UpdateSVDBFileJob extends Job {
		private IDocument fDocument;
		
		public UpdateSVDBFileJob(IDocument doc) {
			super("Update SVDBFile");
			fDocument = doc;
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			IDocument doc;
			IEditorInput ed_in = getEditorInput();
			if (fDocument != null) {
				doc = fDocument;
			} else {
				doc = getDocumentProvider().getDocument(ed_in);
			}
		
			if (doc == null) {
				try {
					throw new Exception();
				} catch (Exception e) {
					fLog.error("Document NULL during UpdateSVDBFileJob", e);
				}
			}
			
			StringInputStream sin = new StringInputStream(doc.get());
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			fLog.debug("--> re-parse file");
			Tuple<SVDBFile, SVDBFile> new_in = fFileIndexParser.parse(
					monitor, sin, fSVDBFilePath, markers);
			fSVDBFile.clearChildren();
			fLog.debug("<-- re-parse file");
		
			if (new_in != null) {
				fSVDBFile = new_in.second();
				fSVDBFilePP = new_in.first();
				if (fSVDBIndex != null) {
					fSVDBIndex.setFile(fSVDBFile);
					fSVDBIndex.setFilePP(fSVDBFilePP);
				}

				addErrorMarkers(markers);
				applyUnprocessedRegions(fSVDBFilePP);
				applyFolding(fSVDBFile, fSVDBFilePP);
				applyOverrideAnnotations(fSVDBFile);
			}

			if (fOutline != null) {
				fOutline.refresh();
			}
			
			synchronized (SVEditor.this) {
				fUpdateSVDBFileJob = null;
				fNeedUpdate = false;
				if (fPendingUpdateSVDBFile) {
					updateSVDBFile(fDocument, true);
				}
			}
			
			return Status.OK_STATUS;
		}
	}
	
	public SVEditor() {
		super();
		
		fMarkers = new ArrayList<SVDBMarker>();
		
		setDocumentProvider(SVEditorDocumentProvider.getDefault());
		
		fCodeScanner = new SVCodeScanner();
		fCharacterMatcher = new SVCharacterPairMatcher();
		SVUiPlugin.getDefault().getPreferenceStore().addPropertyChangeListener(
				fPropertyChangeListener);
		
		fLog = LogFactory.getLogHandle("SVEditor");
		
		// Check in with the plug-in
		SVUiPlugin.getDefault().startRefreshJob();
		
		updateFoldingPrefs();
		updateAutoIndexDelayPref();
	}
	
	protected void updateAutoIndexDelayPref() {
		IPreferenceStore ps = SVUiPlugin.getDefault().getChainedPrefs();
		
		int delay = ps.getInt(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_DELAY);
		
		if (delay == -1) {
			fIncrReparseEn = false;
		} else {
			fIncrReparseEn = true;
			fReparseDelay = delay;
		}
	}

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		super.init(site, input);
		
		site.getPage().addPartListener(this);
	
		if (input instanceof IFileEditorInput) {
			ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
			fFile = ((IFileEditorInput)input).getFile().getFullPath().toOSString();
		} else if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			if (uri.getScheme().equals("plugin")) {
				fFile = "plugin:" + uri.getPath();
			} else {
				fFile = uri.getPath();
			}
		}
		
		fSVDBFile = new SVDBFile(fFile);
		fSVDBFilePP = new SVDBFile(fFile);
		
		// Fixup documents that have \r and not \r\n
		IDocument doc = getDocument();
		int idx=0;
		int replacements=0;
		try {
			while (idx < doc.getLength()) {
				int ch = doc.getChar(idx);
				if (ch == '\r') {
					if (idx+1 < doc.getLength() && doc.getChar(idx+1) != '\n') {
						doc.replace(idx, 1, "\r\n");
						replacements++;
					} else if (idx+1 >= doc.getLength()) {
						// Insert a final '\n'
						doc.replace(idx, 1, "\r\n");
						replacements++;
					}
				}
				idx++;
			}
		} catch (BadLocationException e) {}
		if (replacements > 0) {
			fLog.note("Replaced " + replacements + " occurrences of '\\r' without '\\n' in file " + fFile);
		}

		
//		getSelectionProvider().addSelectionChangedListener(selectionChangedListener);
		
		// Hook into the SVDB management structure
		initSVDBMgr();
		
		updateAutoIndexDelayPref();
	}
	
	
	
	@Override
	public void doSave(IProgressMonitor progressMonitor) {
		super.doSave(progressMonitor);
	
		if (!fIncrReparseEn) {
			updateSVDBFile(getDocument(), true);
		}
		
		// TODO: When the user saves the file, clear any cached information
		// on validity.
	}

	@Override
	public void doSaveAs() {
		super.doSaveAs();
	
		if (!fIncrReparseEn) {
			updateSVDBFile(getDocument(), true);
		}
		
		// TODO: Probably need to make some updates when the name changes
	}

	/**
	 * Called when project settings change. Update our notion of
	 * which index is managing this file
	 */
	public void projectSettingsChanged(SVDBProjectData data) {
		fLog.debug(LEVEL_MID, "projectSettingsChanged: " + fSVDBFilePath);
		synchronized (this) {
			if (fProjectSettingsJob == null) {
				String pname = (data != null)?data.getName():null;
				fProjectSettingsJob = new UpdateProjectSettingsJob(this, pname);
				fProjectSettingsJob.schedule();
				fPendingProjectSettingsUpdate = null;
			} else {
				fPendingProjectSettingsUpdate = data;
			}
		}
	}

	public void int_projectSettingsUpdated(
			final ISVDBIndex 		index, 
			SVDBIndexCollection 	index_mgr) {
		fLog.debug(LEVEL_MIN, "projectSettingsUpdated " + fSVDBFilePath + " - index=" + 
				((index != null)?(index.getTypeID() + "::" + index.getBaseLocation()):"null") + 
				" ; index_mgr=" + 
				((index_mgr != null)?(index_mgr.getProject()):"null"));
		
		final SVActionContributor ac = (SVActionContributor)getEditorSite().getActionBarContributor();
		getEditorSite().getShell().getDisplay().asyncExec(new Runnable() {
			public void run() {
				String msg = "";
				boolean is_indexed = false;
				if (index != null) {
					msg = "Index: " + index.getBaseLocation();
					is_indexed = true;
				} else {
					msg = "Index: None";
				}
				ac.getActionBars().getStatusLineManager().setMessage(msg);
				Image icon = null;
				if (is_indexed) {
					icon = SVUiPlugin.getImage("/icons/vlog_16_16_indexed.gif");
				} else {
					icon = SVUiPlugin.getImage("/icons/vlog_16_16.gif");
				}
				setTitleImage(icon);
			}
		});
		
		synchronized (this) {
			fProjectSettingsJob = null;
			
			if (index == null) {
				// Create a shadow index
				
				// See if this file is part of a project with a
				// configured index
				IFile file = SVFileUtils.findWorkspaceFile(fSVDBFilePath);
				String file_dir = SVFileUtils.getPathParent(fSVDBFilePath);
				
				if (file != null) {
					if (SVDBProjectManager.isSveProject(file.getProject())) {
						SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
						SVDBProjectData pdata = pmgr.getProjectData(file.getProject());
					
						if (pdata != null) {
							index_mgr = pdata.getProjectIndexMgr();
						}
					}
				}
			
				fFileIndexParser = new SVDBShadowIndexParse(index_mgr);
				fSVDBIndex = new SVDBFileOverrideIndex(
						fSVDBFile, fSVDBFilePP, index, index_mgr, fMarkers);
				fSVDBIndex.setIncFilesFinder(
						new SVDBShadowIncludeFilesFinder(file_dir));
				fLog.debug(LEVEL_MIN, "init w/ShadowIndex");
			} else {
				// An index was specified, so proceed normally
				
				// Unhook the index listener from the old index
				ISVDBIndex old_index = null;
				if (fSVDBIndex != null) {
					old_index = fSVDBIndex.getBaseIndex();
				}
				if (old_index != null) {
					old_index.removeChangeListener(this);
				}
			
				// Add a change listener to the new index
				index.addChangeListener(this);
				
				fFileIndexParser = index_mgr;
				fSVDBIndex = new SVDBFileOverrideIndex(
						fSVDBFile, fSVDBFilePP, index, index_mgr, fMarkers);
				fLog.debug(LEVEL_MIN, "init w/RealIndex");
			}
		}
		if (fPendingProjectSettingsUpdate != null) {
			projectSettingsChanged(fPendingProjectSettingsUpdate);
		} else {
			updateSVDBFile(null, false);
		}
	}

	private void initSVDBMgr() {
		IEditorInput ed_in = getEditorInput();
		
		SVActionContributor ac = (SVActionContributor)getEditorSite().getActionBarContributor();
		ac.getActionBars().getStatusLineManager().setMessage("Finding association");
		
		if (ed_in instanceof IURIEditorInput) {
			IURIEditorInput uri_in = (IURIEditorInput)ed_in;
			SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();

			if (uri_in.getURI().getScheme().equals("plugin")) {
				fLog.debug(LEVEL_MIN, "Editor path is in a plugin: " + uri_in.getURI());
				fSVDBFilePath = "plugin:" + uri_in.getURI().getPath();
				fSVDBFilePath = SVFileUtils.normalize(fSVDBFilePath);
				
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
				
				fFileIndexParser = new SVDBIndexCollection(rgy.getIndexCollectionMgr(), plugin);

				// TODO: This argues that we should have an index collection
				// for each plugin index 
				/*
				if (target != null) {
					fLog.debug(LEVEL_MIN, "Found a target plugin library");
					fIndexMgr.addPluginLibrary(rgy.findCreateIndex(
							new NullProgressMonitor(), 
							SVDBIndexRegistry.GLOBAL_PROJECT, target.getId(), 
							SVDBPluginLibIndexFactory.TYPE, null));
				} else {
					fLog.debug(LEVEL_MIN, "Did not find the target plugin library");
				}
				 */
			} else { // regular workspace or filesystem path
				if (ed_in instanceof FileEditorInput) {
					// Regular in-workspace file
					FileEditorInput fi = (FileEditorInput)ed_in;
					fLog.debug(LEVEL_MIN, "Path \"" + fi.getFile().getFullPath() + 
							"\" is in project " + fi.getFile().getProject().getName());
					
					// re-adjust
					
					fSVDBFilePath = "${workspace_loc}" + fi.getFile().getFullPath().toOSString();
					fSVDBFilePath = SVFileUtils.normalize(fSVDBFilePath);
					
					fLog.debug(LEVEL_MIN, "Set SVDBFilePath=" + fSVDBFilePath);
					
					projectSettingsChanged(mgr.getProjectData(fi.getFile().getProject()));
					
					mgr.addProjectSettingsListener(this);
				} else {
					// Outside-workspace file
					fLog.debug(LEVEL_MIN, "URI instance: " + uri_in.getClass().getName());
					fSVDBFilePath = SVFileUtils.normalize(uri_in.getURI().getPath());
					fLog.debug(LEVEL_MIN, "Normalizing file \"" + uri_in.getURI().getPath() + "\" to \"" + fSVDBFilePath + "\"");
					fLog.debug(LEVEL_MIN, "File \"" + fSVDBFilePath + "\" is outside the workspace");

					// Kick off a job to find the relevant index
					projectSettingsChanged(null);
				}
			}
		} else {
			fLog.error("SVEditor input is of type " + ed_in.getClass().getName());
		}
	}

	void updateSVDBFile(IDocument doc, boolean force) {
		fLog.debug(LEVEL_MAX, "updateSVDBFile - fIndexMgr=" + fFileIndexParser);
	
		if (fFileIndexParser != null) {
			if (fUpdateSVDBFileJob == null) {
				synchronized (this) {
					fPendingUpdateSVDBFile = false;
					if (fIncrReparseEn || force) {
						fUpdateSVDBFileJob = new UpdateSVDBFileJob(doc);
						fUpdateSVDBFileJob.schedule(fReparseDelay);
					}
				}
			} else {
				fPendingUpdateSVDBFile = true;
			}
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

		/*
		a = new TextOperationAction(bundle,
				"ContentFormat.", this, ISourceViewer.FORMAT);
		a.setActionDefinitionId("net.sveditor.ui.indent");
		setAction("ContentFormat", a);
		markAsStateDependentAction("Format", true);
		markAsSelectionDependentAction("Format", true);
		 */

		
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
		
		OpenDeclarationAction od_action = new OpenDeclarationAction(bundle, this);
		od_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.declaration");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", od_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", false);
		
		
		FindReferencesAction fr_action = new FindReferencesAction(bundle, this);
		fr_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.find.references");
		setAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", fr_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", false);
		
		OpenTypeAction ot_action = new OpenTypeAction(bundle, this);
		ot_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.type");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenTypeAction", ot_action);
		
		OpenTypeHierarchyAction th_action = new OpenTypeHierarchyAction(bundle, this);
		th_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.type.hierarchy");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenTypeHierarchyAction", th_action);

		OpenObjectsViewAction ov_action = new OpenObjectsViewAction(bundle);
		ov_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.objects");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenObjectsAction", ov_action);

		OpenQuickObjectsViewAction qov_action = new OpenQuickObjectsViewAction(bundle, this);
		qov_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.quick.objects");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenQuickObjectsAction", qov_action);

		OpenQuickOutlineAction qoutv_action = new OpenQuickOutlineAction(bundle, this);
		qoutv_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.quick.outline");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenQuickOutlineAction", qoutv_action);

		OpenQuickHierarchyAction qh_action = new OpenQuickHierarchyAction(bundle, this);
		qh_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.quick.hierarchy");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenQuickHierarchyAction", qh_action);

		OpenDiagForSelectionAction ods_action = new OpenDiagForSelectionAction(bundle, this);
		ods_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.diag.selection");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenDiagForSelectionAction", ods_action);

		IndentAction ind_action = new IndentAction(bundle, "Indent.", this);
		ind_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".indent");
		setAction(SVUiPlugin.PLUGIN_ID + ".svIndentEditorAction", ind_action);
		
		AddBlockCommentAction add_block_comment = new AddBlockCommentAction(
				bundle, "AddBlockComment.", this);
		add_block_comment.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".AddBlockComment");
		add_block_comment.setEnabled(true);
		setAction(SVUiPlugin.PLUGIN_ID + ".svAddBlockCommentAction", add_block_comment);
		
		RemoveBlockCommentAction remove_block_comment = new RemoveBlockCommentAction(
				bundle, "RemoveBlockComment.", this);
		remove_block_comment.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".RemoveBlockComment");
		remove_block_comment.setEnabled(true);
		setAction(SVUiPlugin.PLUGIN_ID + ".svRemoveBlockCommentAction", remove_block_comment);
		
		ToggleCommentAction toggle_comment = new ToggleCommentAction(bundle, "ToggleComment.", this);
		toggle_comment.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".ToggleComment");
		// TODO: Toggle requires more investigation on how to implement
		toggle_comment.setEnabled(true);
		toggle_comment.configure(getSourceViewer(), getSourceViewerConfiguration());
		setAction(SVUiPlugin.PLUGIN_ID + ".svToggleCommentAction", toggle_comment);
		
		OverrideTaskFuncAction ov_tf_action = new OverrideTaskFuncAction(
				bundle, "OverrideTaskFunc.", this);
		ov_tf_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".override.tf.command");
		setAction(SVUiPlugin.PLUGIN_ID + ".override.tf", ov_tf_action);
		
		NextWordAction nw_action = new NextWordAction(
				bundle, "NextWordAction.", this);
		nw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.WORD_NEXT);
		setAction(ITextEditorActionDefinitionIds.WORD_NEXT, nw_action);
		
		PrevWordAction pw_action = new PrevWordAction(
				bundle, "PrevWordAction.", this);
		pw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.WORD_PREVIOUS);
		setAction(ITextEditorActionDefinitionIds.WORD_PREVIOUS, pw_action);
		
		SelNextWordAction sel_nw_action = new SelNextWordAction(
				bundle, "SelNextWordAction.", this);
		sel_nw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.SELECT_WORD_NEXT);
		setAction(ITextEditorActionDefinitionIds.SELECT_WORD_NEXT, sel_nw_action);
		
		SelPrevWordAction sel_pw_action = new SelPrevWordAction(
				bundle, "SelPrevWordAction.", this);
		sel_pw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.SELECT_WORD_PREVIOUS);
		setAction(ITextEditorActionDefinitionIds.SELECT_WORD_PREVIOUS, sel_pw_action);
		
		// Add annotation-action
		SVRulerAnnotationAction action = new SVRulerAnnotationAction(bundle, 
				"Editor.RulerAnnotationSelection.", this, getVerticalRuler());
		setAction(ITextEditorActionConstants.RULER_CLICK, action);
		
	}
	
	public ISVDBIndexIterator getIndexIterator() {
		return fSVDBIndex;
	}
	
	public IDocument getDocument() {
		return getDocumentProvider().getDocument(getEditorInput());
	}
	
	public IAnnotationModel getAnnotationModel() {
		IAnnotationModel ann_model = null;
		
		ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		return ann_model;
	}
	
	public ITextSelection getTextSel() {
		ITextSelection sel = null;
		
		ISelection sel_o = getSelectionProvider().getSelection();
		if (sel_o != null && sel_o instanceof ITextSelection) {
			sel = (ITextSelection)sel_o;
		}
		
		return sel;
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
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenTypeAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenTypeHierarchyAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenObjectsAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenQuickObjectsAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenQuickOutlineAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenQuickHierarchyAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenDiagForSelectionAction");
		
		addAction(menu, ITextEditorActionConstants.GROUP_FIND,
				SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction");
		
		addGroup(menu, ITextEditorActionConstants.GROUP_EDIT,
				"net.sf.sveditor.ui.source.menu");
		
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
		
		getSite().getPage().removePartListener(this);
		
		if (fOutline != null) {
			fOutline.dispose();
			fOutline = null;
		}
		if (fCharacterMatcher != null) {
			fCharacterMatcher.dispose();
			fCharacterMatcher = null;
		}

		if (getSelectionProvider() != null) {
			getSelectionProvider().removeSelectionChangedListener(selectionChangedListener);
		}
		
		SVCorePlugin.getDefault().getProjMgr().removeProjectSettingsListener(this);
		SVUiPlugin.getDefault().getPreferenceStore().removePropertyChangeListener(
				fPropertyChangeListener);
		
		// Remove handles to shadow index
		fSVDBIndex = null;
		fFileIndexParser  = null;

		// Remove the resource listener
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
	}
	
	public SVSourceViewerConfiguration getSourceViewerConfig() {
		return (SVSourceViewerConfiguration)getSourceViewerConfiguration();
	}
	
	public ITextViewer getTextViewer() {
		return (ITextViewer)getSourceViewer();
	}

	public void createPartControl(Composite parent) {
		
		setSourceViewerConfiguration(new SVSourceViewerConfiguration(this,SVUiPlugin.getDefault().getPreferenceStore()));
		
		super.createPartControl(parent);
		
	    ProjectionViewer viewer = (ProjectionViewer)getSourceViewer();

	    fProjectionSupport = new ProjectionSupport(viewer, getAnnotationAccess(), getSharedColors());
	    fProjectionSupport.install();
	    
	    //turn projection mode on
	    if (getFoldingPref(SVEditorPrefsConstants.P_FOLDING_ENABLE)) {
	    	viewer.doOperation(ProjectionViewer.TOGGLE);
	    }
	    
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
		
		getSourceViewer().getSelectionProvider().addSelectionChangedListener(selectionChangedListener);
		
		/**
		 * Add semantic highlighting
		 */
		
	}
	
	@Override
	protected ISourceViewer createSourceViewer(
			Composite 			parent,
			IVerticalRuler 		ruler, 
			int 				styles) {
		ISourceViewer viewer = new ProjectionViewer(parent, ruler,
				getOverviewRuler(), isOverviewRulerVisible(), styles);

		// ensure decoration support has been created and configured.
		getSourceViewerDecorationSupport(viewer);

		return viewer;		
	}

	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}
	
	public List<SVDBFilePath> getSVDBFilePath() {
		if (fSVDBIndex != null) {
			return fSVDBIndex.getFilePath(fSVDBFilePath);
		} else {
			return null;
		}
	}
	
	public String getFilePath() {
		/*
		IEditorInput ed_in = getEditorInput();
		String ret = null;
		
		if (ed_in instanceof IFileEditorInput) {
			ret = ((IFileEditorInput)ed_in).getFile().getFullPath().toOSString();
		} else if (ed_in instanceof IURIEditorInput) {
			ret = ((IURIEditorInput)ed_in).getURI().getPath();
		}
		
		return ret;
		 */
		return fSVDBFilePath;
	}
	
	
	public void setSelection(ISVDBItemBase it, boolean set_cursor) {
		int start = -1;
		int end   = -1;
		
		if (it.getLocation() != null) {
			start = it.getLocation().getLine();
			
			if (it instanceof ISVDBScopeItem &&
					((ISVDBScopeItem)it).getEndLocation() != null) {
				end = ((ISVDBScopeItem)it).getEndLocation().getLine();
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
			int offset    = doc.getLineOffset(start);
			int last_line = doc.getLineOfOffset(doc.getLength()-1);
			
			if (end > last_line) {
				end = last_line;
			}
			int offset_e = doc.getLineOffset(end);
			setHighlightRange(offset, (offset_e-offset), false);
			if (set_cursor) {
				getSourceViewer().getTextWidget().setCaretOffset(offset);
			}
			selectAndReveal(offset, 0, offset, (offset_e-offset));
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}
	
	public ISourceViewer sourceViewer() {
		return getSourceViewer();
	}
	
	public void index_changed(int reason, SVDBFile file) {
		// TODO Auto-generated method stub
//		System.out.println("index_changed");
	}

	public void index_rebuilt() {
		if (Display.getDefault() == null) {
			fNeedUpdate = true;
			return;
		}
		
		// Force a rebuild to pick up latest errors
		// Note: isPartVisible() is a display-thread protected method
		Display.getDefault().asyncExec(new Runnable() {
			public void run() {
				if (getSite() != null && getSite().getPage().isPartVisible(SVEditor.this)) {
					if (fSVDBIndex.getBaseIndex() == null) {
						// Try re-checking
						projectSettingsChanged(null);
					}
					updateSVDBFile(getDocument(), false);
				} else {
					// Store the knowledge that we need an update for later
					fNeedUpdate = true;
				}
			}
		});
	}

	// IPartListener methods
	public void partActivated(IWorkbenchPart part) {
		if (fNeedUpdate) {
			updateSVDBFile(getDocument(), true);
		}
	}

	public void partBroughtToTop(IWorkbenchPart part) { }
	public void partClosed(IWorkbenchPart part) { }
	public void partDeactivated(IWorkbenchPart part) { }
	public void partOpened(IWorkbenchPart part) { }

	/**
	 * Clears error annotations
	 */
	@SuppressWarnings("unchecked")
	private void clearErrors() {
		/*
		System.out.println("getDocumentProvider: " + getDocumentProvider());
		System.out.println("getEditorInput: " + getEditorInput());
		System.out.println("getAnnotationMode: " + getDocumentProvider().getAnnotationModel(getEditorInput()));
		 */
		if (getDocumentProvider() == null || getEditorInput() == null ||
				getDocumentProvider().getAnnotationModel(getEditorInput()) == null) {
			return;
		}
		IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();

		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals("org.eclipse.ui.workbench.texteditor.error")) {
				ann_model.removeAnnotation(ann);
			}
		}
	}

	/**
	 * Add error annotations from the 
	 */
	private void addErrorMarkers(List<SVDBMarker> markers) {
		// Mostly used in testing mode
		if (getDocumentProvider() == null || getEditorInput() == null ||
				getDocumentProvider().getAnnotationModel(getEditorInput()) == null) {
			return;
		}
		clearErrors();
		IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());

		
		
		for (SVDBMarker marker : markers) {
			Annotation ann = null;
			int line = -1;
			
			if (marker.getMarkerType() == MarkerType.Error) {
				ann = new Annotation(
						"org.eclipse.ui.workbench.texteditor.error", 
						false, marker.getMessage());
				line = marker.getLocation().getLine();
			}

			if (ann != null) {
				IDocument doc = getDocumentProvider().getDocument(getEditorInput());
				try {
					Position pos = new Position(doc.getLineOffset(line-1));
					ann_model.addAnnotation(ann, pos);
				} catch (BadLocationException e) {
					e.printStackTrace();
				}
			}
		}
	}
	
	private void applyUnprocessedRegions(SVDBFile file_pp) {
		List<SVDBUnprocessedRegion> unprocessed_regions = new ArrayList<SVDBUnprocessedRegion>();
		IDocument doc = getDocument();
		IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		clearUnprocessedRegionAnnotations();
		collectUnprocessedRegions(unprocessed_regions, file_pp);
		
		for (SVDBUnprocessedRegion r : unprocessed_regions) {
			SVDBLocation start = r.getLocation();
			SVDBLocation end = r.getEndLocation();

			if (start == null || end == null) {
				continue;
			}
			
			Annotation ann_1 = new Annotation(SVUiPlugin.PLUGIN_ID + ".disabledRegion", false, "");
			try {
				int line1 = doc.getLineOffset((start.getLine()>0)?start.getLine()-1:0);
				int line2 = doc.getLineOffset(end.getLine());
				ann_model.addAnnotation(ann_1, new Position(line1, (line2-line1)));
			} catch (BadLocationException e) {}
		}
	}
	
	private void collectUnprocessedRegions(List<SVDBUnprocessedRegion> unprocessed_regions, ISVDBChildParent scope) {
		for (ISVDBChildItem ci : scope.getChildren()) {
			if (ci.getType() == SVDBItemType.UnprocessedRegion) {
				unprocessed_regions.add((SVDBUnprocessedRegion)ci);
			}
		}
	}

	@SuppressWarnings("unchecked")
	private void applyOverrideAnnotations(SVDBFile file) {
		SVDBFindSuperClass super_finder = new SVDBFindSuperClass(getIndexIterator());
		List<SVDBClassDecl> classes = new ArrayList<SVDBClassDecl>();
		
		// First, clear existing override annotations
		ISourceViewer sv = getSourceViewer();
		if (sv == null) {
			return;
		}
		IAnnotationModel ann_model = sv.getAnnotationModel();
		IDocument doc = getDocument();
		
		if (ann_model == null) {
			return;
		}
		
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals(SVUiPlugin.PLUGIN_ID + ".methodOverride")) {
				ann_model.removeAnnotation(ann);
			}
		}
	
		// Collect all classes declared in this file
		collectClasses(classes, fSVDBFile);
		
		// For each class, 
		// - find all methods declared in the super-class structure
		// - find methods declared in this class that override super-structure methods
		for (SVDBClassDecl cls : classes) {
			SVDBClassDecl super_cls = super_finder.find(cls);
			
			if (super_cls != null) {
				Set<String> processed_classes = new HashSet<String>();
				Set<SVDBTask> super_methods = new HashSet<SVDBTask>();
				List<SVDBTask> override_tf = new ArrayList<SVDBTask>();
				collectSuperClassMethods(processed_classes, super_methods, super_finder, super_cls);
				
				collectOverrideMethods(cls, super_methods, override_tf);
				
				// Apply override annotations
				for (SVDBTask tf : override_tf) {
					
					SVDBTask target_t = null;
					for (SVDBTask ti : super_methods) {
						if (ti.getName().equals(tf.getName())) {
							target_t = ti;
							break;
						}
					}
					
					if (target_t == null) {
						// unexpected
						continue;
					}
					
					Annotation ann = new SVOverrideMethodAnnotation(target_t, 
							"overrides " + SVDBItem.getName(target_t.getParent()) + "::" + target_t.getName());
					
					try {
						int line = tf.getLocation().getLine();
						if (line > 0) {
							line = doc.getLineOffset(line-1);
						} else {
							line = doc.getLineOffset(0);
						}
						
						ann_model.addAnnotation(ann, new Position(line, 0));
					} catch (BadLocationException e) {
						e.printStackTrace();
					}
				}
			}
		}
	}

	/**
	 * Collects all class declarations from this file
	 */
	private void collectClasses(List<SVDBClassDecl> classes, ISVDBChildParent scope) {
		for (ISVDBChildItem ci : scope.getChildren()) {
			if (ci.getType() == SVDBItemType.ClassDecl) {
				classes.add((SVDBClassDecl)ci);
			} else if (ci.getType() == SVDBItemType.PackageDecl ||
					ci.getType() == SVDBItemType.ModuleDecl ||
					ci.getType() == SVDBItemType.InterfaceDecl ||
					ci.getType() == SVDBItemType.ProgramDecl) {
				collectClasses(classes, (ISVDBChildParent)ci);
			}
		}
	}
	
	private void collectSuperClassMethods(
			Set<String>				processed_classes, // avoid accidental infinite recursion
			Set<SVDBTask>			super_methods,
			SVDBFindSuperClass		super_class_finder,
			SVDBClassDecl			cls) {

		processed_classes.add(cls.getName());
		for (ISVDBChildItem ci : cls.getChildren()) {
			// Look for tasks/functions here
			if (ci.getType() == SVDBItemType.Function ||
					ci.getType() == SVDBItemType.Task) {
				boolean found = false;
				String name = SVDBItem.getName(ci);
				
				if (!name.equals("new")) {
					for (SVDBTask t : super_methods) {
						if (t.getName().equals(name)) {
							found = true;
							break;
						}
					}

					if (!found) {
						super_methods.add((SVDBTask)ci);
					}
				}
			}
		}
		
		SVDBClassDecl super_cls = super_class_finder.find(cls);
		
		if (super_cls != null) {
			if (!processed_classes.contains(super_cls.getName())) {
				collectSuperClassMethods(processed_classes, super_methods, super_class_finder, super_cls);
			}
		}
	}
			
	private void collectOverrideMethods(
			SVDBClassDecl	 		cls,
			Set<SVDBTask>			super_methods,
			List<SVDBTask>			override_tf) {
		for (ISVDBChildItem ci : cls.getChildren()) {
			if (ci.getType() == SVDBItemType.Task || ci.getType() == SVDBItemType.Function) {
				// 
				SVDBTask t = (SVDBTask)ci;
				boolean found = false;
				for (SVDBTask ti : super_methods) {
					if (ti.getName().equals(t.getName())) {
						found = true;
						break;
					}
				}
				if (found) {
					override_tf.add(t);
				}
			}
		}
	}

	@SuppressWarnings("rawtypes")
	private Annotation [] computeDifferences(ProjectionAnnotationModel model, List<Tuple<Position, Boolean>> regions) {
		List<Annotation> deletions = new ArrayList<Annotation>();

		Iterator ann_it = model.getAnnotationIterator();
		while (ann_it.hasNext()) {
			Object ann_o = ann_it.next();
			
			if (ann_o instanceof ProjectionAnnotation) {
				ProjectionAnnotation ann_p = (ProjectionAnnotation)ann_o;
				Position pos = model.getPosition(ann_p);
				
				// See if this already exists
				int idx = -1;
				for (int i=0; i<regions.size(); i++) {
					Tuple<Position, Boolean> tr = regions.get(i);
					// The annotation model attempts to update the bounds of the projection
					// annotation when the document changes. It mostly successful, but 
					// seems to get tripped up when pasting or deleting a block of content
					// from within an folding region. Work around this by recognizing that
					// a region that starts at the same point is the same even if the
					// length has changed.
					if (tr.first().equals(pos) ||
							tr.first().getOffset() == pos.getOffset()) {
						idx = i;
						break;
					}
				}
				
				if (idx != -1) {
					regions.remove(idx);
				} else {
					deletions.add(ann_p);
				}
			}
		}
		
		return deletions.toArray(new Annotation[deletions.size()]);
	}
	
	private void applyFolding(SVDBFile file, SVDBFile file_pp) {
	    ProjectionViewer viewer =(ProjectionViewer)getSourceViewer();
	    if (viewer == null) {
	    	return;
	    }
	    ProjectionAnnotationModel ann_model = viewer.getProjectionAnnotationModel();
	    
	    if (ann_model == null) {
	    	return;
	    }
	    
		List<Tuple<Position, Boolean>> positions = 
				new ArrayList<Tuple<Position,Boolean>>();
		HashMap<ProjectionAnnotation, Position> newAnnotations = new HashMap<ProjectionAnnotation, Position>();
		
		collectFoldingRegions(file.getLocation().getFileId(), file, positions);
		
		IDocument doc = getDocument();
		for (ISVDBChildItem ci : file_pp.getChildren()) {
			if (ci.getType() == SVDBItemType.UnprocessedRegion) {
				SVDBUnprocessedRegion ur = (SVDBUnprocessedRegion)ci;
				SVDBLocation start = ur.getLocation();
				SVDBLocation end = ur.getEndLocation();
			
				if (start != null && end != null) {
					try {
						int start_l = start.getLine();
						int end_l = end.getLine(); // this is the `endif or `else
						
						if (start_l > 0) {
							start_l--;
						}
					
						// We want to show the ending directive
						end_l--;
						
						if (start_l < end_l) {
							int start_o = doc.getLineOffset(start_l);
							int end_o = doc.getLineOffset(end_l);
							
							boolean init_folded = false;
							
							if (fInitialFolding) {
								init_folded = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_UNPROCESSED);
							}
							
							positions.add(new Tuple<Position, Boolean>(
									new Position(start_o, (end_o-start_o)), init_folded));
									
						}
					} catch (BadLocationException e) {}
				}
			}
		}
	
		Annotation deletions[] = computeDifferences(ann_model, positions);
		
		Annotation annotations[] = new Annotation[positions.size()];
		
		for (int i=0; i<positions.size(); i++) {
			Tuple<Position, Boolean> pos = positions.get(i);
			ProjectionAnnotation ann = new ProjectionAnnotation(pos.second());
			newAnnotations.put(ann, pos.first());
			annotations[i] = ann;
		}

		if (deletions.length != 0 || newAnnotations.size() != 0) {
			ann_model.modifyAnnotations(deletions, newAnnotations, 
					new Annotation[] {});
		}
		
		fInitialFolding = false;
	}
	
	private static final Set<SVDBItemType>				fFoldingRegions;
	private static final Set<SVDBItemType>				fRecurseFoldingRegions;
	
	static {
		fFoldingRegions = new HashSet<SVDBItemType>();
		fRecurseFoldingRegions = new HashSet<SVDBItemType>();
		fFoldingRegions.add(SVDBItemType.ModuleDecl);
		fRecurseFoldingRegions.add(SVDBItemType.ModuleDecl);
		fFoldingRegions.add(SVDBItemType.InterfaceDecl);
		fRecurseFoldingRegions.add(SVDBItemType.InterfaceDecl);
		fFoldingRegions.add(SVDBItemType.ClassDecl);
		fRecurseFoldingRegions.add(SVDBItemType.ClassDecl);
		fFoldingRegions.add(SVDBItemType.PackageDecl);
		fRecurseFoldingRegions.add(SVDBItemType.PackageDecl);
		fFoldingRegions.add(SVDBItemType.ProgramDecl);
		fRecurseFoldingRegions.add(SVDBItemType.ProgramDecl);
		
		fFoldingRegions.add(SVDBItemType.Task);
		fFoldingRegions.add(SVDBItemType.Function);
		fFoldingRegions.add(SVDBItemType.Constraint);
	}
	
	private void collectFoldingRegions(
			int 							file_id, 
			ISVDBChildParent 				scope, 
			List<Tuple<Position,Boolean>>	positions) {
		IDocument doc = getDocument();
		for (ISVDBChildItem ci : scope.getChildren()) {
			if (fFoldingRegions.contains(ci.getType())) {
				ISVDBEndLocation el = (ISVDBEndLocation)ci;
				SVDBLocation start = ci.getLocation();
				SVDBLocation end = el.getEndLocation();
			
				if (start != null && end != null) {
					int it_file_id = start.getFileId();
					
					if (file_id == -1 || it_file_id == file_id) {
						try {
							int start_l = start.getLine();
							int end_l = end.getLine();
							if (start_l != end_l) {
								if (start_l > 0) {
									start_l--;
								}

								int start_o = doc.getLineOffset(start_l);
								int end_o = doc.getLineOffset(end_l);
								
								boolean fold_default = false;
							
								if (fInitialFolding) {
									switch (ci.getType()) {
									case ModuleDecl:
										fold_default = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_MODULES);
										break;
									case ClassDecl:
										fold_default = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_CLASSES);
										break;
									case InterfaceDecl:
										fold_default = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_INTERFACES);
										break;
									default:
										break;
									}
								}

								positions.add(new Tuple<Position, Boolean>(
										new Position(start_o, (end_o-start_o)),
										fold_default));
							}
						} catch (BadLocationException e) {}
						
						if (fRecurseFoldingRegions.contains(ci.getType())) {
							// Must recurse
							collectFoldingRegions(file_id, (ISVDBChildParent)ci, positions);
						}
					}
				}
			}
		}
	}
	
	private void clearUnprocessedRegionAnnotations() {
		IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		// Clear annotations
		@SuppressWarnings("unchecked")
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			
			if (ann.getType().equals("net.sf.sveditor.ui.disabledRegion")) {
				ann_model.removeAnnotation(ann);
			}
		}
	}
	
	private void clearOccurrenceHighlight() {
		IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		// Clear annotations
		@SuppressWarnings("unchecked")
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals("net.sf.sveditor.ui.occurrences")) {
				ann_model.removeAnnotation(ann);
			}
		}
	}

	private void updateWordSelectionHighlight() {
		if (getSourceViewer() == null) {
			return;
		}
		ISelectionProvider sel_p = getSourceViewer().getSelectionProvider();
		
		if (sel_p == null) {
			return;
		}
		
		ITextSelection sel = (ITextSelection)sel_p.getSelection();
		
		clearOccurrenceHighlight();
		
		if (sel.getText() != null && !sel.getText().trim().equals("")) {
			boolean single_word = true;
			
			for (int i=0; i<sel.getText().length(); i++) {
				char ch = sel.getText().charAt(i);
				if (Character.isWhitespace(ch)) {
					single_word = false;
					break;
				}
			}
			
			if (single_word) {
				IDocument doc = getDocumentProvider().getDocument(getEditorInput());
				FindReplaceDocumentAdapter finder = new FindReplaceDocumentAdapter(doc);
				IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
				
				// Iterate through the document
				int start = 0;
				while (true) {
					IRegion region = null;
					
					try {
						String selected_text = SVUiPlugin.shouldEscapeFindWordPattern() ? 
								Pattern.quote(sel.getText()) : sel.getText();
						region = finder.find(start, selected_text, true, true, true, false);
					} catch (BadLocationException e) {}
					
					if (region != null) {
						Annotation ann = new Annotation(
								"net.sf.sveditor.ui.occurrences",
								false, "");
						Position position = new Position(region.getOffset(), region.getLength());
						ann_model.addAnnotation(ann, position);
						
						start = region.getOffset()+region.getLength();
					} else {
						break;
					}
				}
			}
		}
	}
	
	@Override
	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		if (adapter.equals(IContentOutlinePage.class)) {
			if (fOutline == null) {
				fOutline = new SVOutlinePage(this);
			}
			return fOutline;
		}
		return super.getAdapter(adapter);
	}
	

	private void updateFoldingPrefs() {
		fFoldingPrefs.clear();
		IPreferenceStore ps = SVUiPlugin.getDefault().getChainedPrefs();
		for (String fp : SVEditorPrefsConstants.P_FOLDING_PREFS) {
			fFoldingPrefs.put(fp, ps.getBoolean(fp));
		}
	}
	
	private boolean getFoldingPref(String key) {
		if (fFoldingPrefs.containsKey(key)) {
			return fFoldingPrefs.get(key);
		} else {
			return false;
		}
	}
	
	private IPropertyChangeListener fPropertyChangeListener = 
		new IPropertyChangeListener() {

			public void propertyChange(PropertyChangeEvent event) {
				SVColorManager.clear();
				getCodeScanner().updateRules();
				if (getSourceViewer() != null && getSourceViewer().getTextWidget() != null) {
					getSourceViewer().getTextWidget().redraw();
					getSourceViewer().getTextWidget().update();
				}
				
				if (SVEditorPrefsConstants.P_FOLDING_PREFS.contains(event.getProperty())) {
					updateFoldingPrefs();
				} else if (event.getProperty().equals(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_DELAY)) {
					updateAutoIndexDelayPref();
				}
			}
	};
	
	private ISelectionChangedListener selectionChangedListener = 
			new ISelectionChangedListener() {
				
		public void selectionChanged(SelectionChangedEvent event) {
			if (event.getSelection() instanceof ITextSelection) {
				if (!fOccurrenceHighlightDebounceActive) {
					fOccurrenceHighlightDebounceActive = true;
					Display.getDefault().timerExec(500, occurrenceHighlightDebounce);
				}
			}
		}
	};
	
	private Runnable occurrenceHighlightDebounce = new Runnable() {
		
		public void run() {
			fOccurrenceHighlightDebounceActive = false;
			updateWordSelectionHighlight();
		}
	};

	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getResource() != null && 
				event.getResource().getFullPath().toOSString().equals(fFile)) {
			// Re-parse the file and update markers if the file changes 
			// outside the editor. 
			updateSVDBFile(getDocument(), true);
		}
	}
	
}
